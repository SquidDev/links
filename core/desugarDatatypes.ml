(** Converts the {!Sugartypes.Datatype.t} representation of types into the {!Types.typ}
    representation.

    This remove type variables, and ensures that their kinds and subkinds are consistent. *)

open CommonTypes
open Errors
open List
open Parse
open SourceCode
open SourceCode.WithPos
open Sugartypes
open Types
open Utility

let internal_error message = Errors.internal_error ~filename:"desugarDatatypes.ml" ~message

let duplicate_var pos var =
  Type_error (pos, Printf.sprintf "Multiple definitions of type variable `%s'." var)

(** Construct an error for when a type alias has free variables within it. *)
let free_type_variable pos name =
  if name.[0] = '_' || name.[0] = '$' then Type_error (pos, "Unbound anonymous type variable.")
  else Type_error (pos, Printf.sprintf "Unbound type variable `%s'." name)

(** Check that no datatype is left un-desugared. *)
let all_datatypes_desugared =
  object (self)
    inherit SugarTraversals.predicate as super

    val all_desugared = true

    method satisfied = all_desugared

    method! datatype' =
      function
      | _, None -> {<all_desugared = false>}
      | _ -> self

    method! phrasenode =
      function
      | TableLit (_, (_, None), _, _, _) -> {<all_desugared = false>}
      | p -> super#phrasenode p
  end

(** Determine if this is an "anonymous" effect type variable, and so introduced within a simple
    arrow (->, ~>, -@, ~>) *)
let is_anon_effect = function
  | Datatype.Open ("$anon", None, `Rigid) -> true
  | _ -> false

(** If this function type is exclusively composed of anonymous effect type variables. Or rather,
    there are no explicitly mentioned effect variables? *)
let all_anon_effects =
  object (o)
    inherit SugarTraversals.predicate as super

    val all_anon = true

    method satisfied = all_anon

    method! datatypenode =
      let open Datatype in
      function
      | (Function (_, (_, eff_var), _) | Lolli (_, (_, eff_var), _))
        when not (is_anon_effect eff_var) ->
          {<all_anon = false>}
      | ty -> super#datatypenode ty

    method recursive_function (bind, _, (_, fl), loc, dt, pos) =
      let o = o#binder bind in
      let o = o#funlit fl in
      let o = o#location loc in
      let o = o#option (fun x -> x#datatype') dt in
      o#position pos
  end

(** The active environment of type variables.

    The variable environment stores bound variables (such as those bound in recursive/forall types,
    or used in phrases of this definition). Variables which are not within the environment are
    added to it, and the updated environment passed to the next term. *)
module VarEnv = struct
  (** A definition of a type variable. This provides enough information to reconstruct a
      {!Types.meta_type_var_non_rec_basis} should we gather more information about the variable. *)
  type def =
    { name : string;  (** This definition's name. *)
      var : int;  (** The unique identifier for this variable. *)
      freedom : CommonTypes.freedom;
      subkind : CommonTypes.subkind option;
          (** The denoted subkind, or {!None} if not currently known. *)
      meta_var : Types.meta_var;
      usage : Position.t
          (** One possible usage-point of this variable, used for error reporting. This will
              generally be the first, but most specific use-site. *)
      }

  type t =
    { tyvars : def StringMap.t;  (** A lookup of all type variables in this environment. *)
      vars : def list;
          (** A list of all type variables in reverse order to that in which they were seen. *)
      implicit_effect : bool
          (** Whether this environment should use a shared effect variable for implicit effects. *)
      }

  let empty = { tyvars = StringMap.empty; implicit_effect = false; vars = [] }

  let kind_of { meta_var; _ } =
    match meta_var with
    | `Type _ -> PrimaryKind.Type
    | `Row _ -> PrimaryKind.Row
    | `Presence _ -> PrimaryKind.Presence

  let kind_error pos kind def =
    TypeVarKindMismatch
      { name = def.name;
        a_kind = kind_of def;
        a_subkind = def.subkind;
        a_pos = def.usage;
        b_kind = kind;
        b_subkind = None;
        b_pos = pos
      }

  (** Create a variable and return the updated scoped, meta var, and definition. *)
  let add_var' factory pos (name, subkind, freedom) ({ tyvars; vars; _ } as scp) :
      t * 'a Unionfind.point * def =
    let var = Types.fresh_raw_variable () in
    let subkind' = opt_app identity default_subkind subkind in
    let point = Unionfind.fresh (`Var (var, subkind', freedom)) in
    let meta_var = factory point in
    let def = { name; var; subkind; freedom; meta_var; usage = pos } in
    ({ scp with tyvars = StringMap.add name def tyvars; vars = def :: vars }, point, def)

  (** Create a variable and return the updated scope and definition. *)
  let add_def factory pos var env =
    let ve, _, d = add_var' factory pos var env in
    (ve, d)

  (** Create a variable and return the updated scope and meta_var. *)
  let add_var factory pos var env =
    let ve, p, _ = add_var' factory pos var env in
    (ve, p)

  (** Map a variable, possibly generating a fresh type name. *)
  let map_var var { implicit_effect; _ } =
    let module SC = SugarConstructors.SugartypesPositions in
    match var with
    | "$eff", None, `Rigid when implicit_effect -> var
    | ("$" | "$eff"), None, freedom -> SC.fresh_known_type_variable freedom
    | _ -> var

  (** Check the subkind of a definition is consistent with its usage, updating it if needed. *)
  let update_subkind pos (name, sk, _) scp point def =
    match (sk, def.subkind) with
    | None, _ -> (scp, point)
    | Some sk, None ->
        let def' = { def with subkind = Some sk; usage = pos } in
        Unionfind.change point (`Var (def.var, sk, def.freedom));
        ( { scp with
            tyvars = StringMap.add name def' scp.tyvars;
            vars = List.map (fun x -> if x.name = def.name then def' else x) scp.vars
          },
          point )
    | Some ska, Some skb when ska = skb -> (scp, point)
    | a_subkind, b_subkind ->
        raise
          (TypeVarKindMismatch
             { name;
               a_kind = kind_of def;
               a_subkind;
               a_pos = def.usage;
               b_kind = kind_of def;
               b_subkind;
               b_pos = pos
             })

  let lookup_tvar pos var ({ tyvars; _ } as scp) =
    let ((name, _, _) as var) = map_var var scp in
    match StringMap.find_opt name tyvars with
    | Some ({ meta_var = `Type v; _ } as d) -> update_subkind pos var scp v d
    | Some x -> raise (kind_error pos PrimaryKind.Type x)
    | None -> add_var (fun x -> `Type x) pos var scp

  let lookup_rvar pos var ({ tyvars; _ } as scp) =
    let ((name, _, _) as var) = map_var var scp in
    match StringMap.find_opt name tyvars with
    | Some ({ meta_var = `Row v; _ } as d) -> update_subkind pos var scp v d
    | Some x -> raise (kind_error pos PrimaryKind.Row x)
    | None -> add_var (fun x -> `Row x) pos var scp

  let lookup_pvar pos var ({ tyvars; _ } as scp) =
    let ((name, _, _) as var) = map_var var scp in
    match StringMap.find_opt name tyvars with
    | Some ({ meta_var = `Presence v; _ } as d) -> update_subkind pos var scp v d
    | Some x -> raise (kind_error pos PrimaryKind.Presence x)
    | None -> add_var (fun x -> `Presence x) pos var scp

  let close_over = function
    | { subkind = Some sk; _ } -> sk
    | { subkind = None; var; freedom; meta_var; _ } ->
        let rebuilt = `Var (var, default_subkind, freedom) in
        ( match meta_var with
        | `Type point -> Unionfind.change point rebuilt
        | `Row point -> Unionfind.change point rebuilt
        | `Presence point -> Unionfind.change point rebuilt );
        default_subkind

  let close_all { tyvars; _ } = StringMap.iter (fun _ x -> close_over x |> ignore) tyvars

  (** Close a variable, and then return a scope without it. *)
  let close name ~inner ~outer:({ tyvars; vars; _ } as outer) =
    StringMap.find name inner.tyvars |> close_over |> ignore;
    { outer with
      tyvars = StringMap.update name (fun _ -> StringMap.find_opt name tyvars) inner.tyvars;
      vars =
        List.fold_right (fun x vs ->
            if x.name = name || StringMap.mem x.name tyvars then vs else x :: vs) inner.vars vars
    }
end

module Desugar = struct
  open Datatype

  let primary_kind_of_type_arg = function
    | Type _ -> PrimaryKind.Type
    | Row _ -> PrimaryKind.Row
    | Presence _ -> PrimaryKind.Presence

  let rec datatype (alias_env : Types.tycon_environment) (ve : VarEnv.t) { node = dt; pos } :
      VarEnv.t * Types.typ =
    let datatype = datatype alias_env in
    match dt with
    | TypeVar var ->
        let ve, v = VarEnv.lookup_tvar pos var ve in
        (ve, `MetaTypeVar v)
    | QualifiedTypeApplication _ -> failwith "Unexpected QualifiedTypeApplication"
    | Function (f, e, t) ->
        let ve, f = fold_map datatype ve f in
        let ve, e = effect_row alias_env pos ve e in
        let ve, t = datatype ve t in
        (ve, `Function (Types.make_tuple_type f, e, t))
    | Lolli (f, e, t) ->
        let ve, f = fold_map datatype ve f in
        let ve, e = effect_row alias_env pos ve e in
        let ve, t = datatype ve t in
        (ve, `Lolli (Types.make_tuple_type f, e, t))
    | Mu (name, t) ->
        let vi, point, { VarEnv.var; _ } =
          VarEnv.add_var' (fun x -> `Type x) pos (name, None, `Flexible) ve
        in
        let vi, t = datatype vi t in
        let ve = VarEnv.close name ~inner:vi ~outer:ve in
        Unionfind.change point (`Recursive (var, t));
        (ve, `MetaTypeVar point)
    | Forall (qs, t) ->
        let vi, qs' = make_forall ve pos qs in
        let vi, t = datatype vi t in
        (close_forall ~outer:ve vi qs, `ForAll (Types.box_quantifiers qs', t))
    | Unit -> (ve, Types.unit_type)
    | Tuple ks ->
        let labels = List.map string_of_int (Utility.fromTo 1 (1 + length ks))
        and unit = Types.make_empty_closed_row ()
        and present (s, x) = (s, `Present x)
        and ve, ks = fold_map datatype ve ks in
        (ve, `Record (fold_right2 (curry (Types.row_with -<- present)) labels ks unit))
    | Record r ->
        let ver, r = row alias_env pos ve r in
        (ver, `Record r)
    | Variant r ->
        let ver, r = row alias_env pos ve r in
        (ver, `Variant r)
    | Effect r ->
        let ver, r = row alias_env pos ve r in
        (ver, `Effect r)
    | Table (r, w, n) ->
        let ve, r = datatype ve r in
        let ve, w = datatype ve w in
        let ve, n = datatype ve n in
        (ve, `Table (r, w, n))
    | List k ->
        let ve, k = datatype ve k in
        (ve, `Application (Types.list, [ `Type k ]))
    | TypeApplication (name, ts) -> (
        (* Matches kinds of the quantifiers against the type arguments.
         * Returns Types.type_args based on the given frontend type arguments. *)
        let match_quantifiers qs =
          let match_kinds tyarg_number (q, t) =
            let q_kind = primary_kind_of_quantifier q in
            let t_kind = primary_kind_of_type_arg t in
            if q_kind <> t_kind then
              raise
                (TypeApplicationKindMismatch
                   { pos;
                     name;
                     tyarg_number;
                     expected = PrimaryKind.to_string q_kind;
                     provided = PrimaryKind.to_string t_kind
                   })
            else (q, t)
          in
          try
            let ts = ListUtils.zip' qs ts in
            let ve, ts =
              fold_mapi
                (fun i ve (q, t) ->
                  let q, t = match_kinds i (q, t) in
                  match subkind_of_quantifier q with
                  | _, Restriction.Effect -> effect_type_arg alias_env pos ve t
                  | _ -> type_arg alias_env pos ve t )
                ve ts
            in
            (ve, ts)
          with ListUtils.Lists_length_mismatch ->
            raise
              (TypeApplicationArityMismatch
                 { pos; name; expected = List.length qs; provided = List.length ts })
        in
        match Env.String.find alias_env name with
        | None -> raise (UnboundTyCon (pos, name))
        | Some (`Alias (qs, _)) ->
            let ve, ts = match_quantifiers qs in
            (ve, Instantiate.alias name ts alias_env)
        | Some (`Abstract abstype) ->
            (* TODO: check that the kinds match up *)
            let ve, ts = fold_map (type_arg alias_env pos) ve ts in
            (ve, `Application (abstype, ts))
        | Some (`Mutual (qs, tygroup_ref)) ->
            (* Check that the quantifiers / kinds match up, then generate a `RecursiveApplication. *)
            let ve, r_args = match_quantifiers qs in
            let r_unwind args dual =
              let _, body = StringMap.find name !tygroup_ref.type_map in
              let body = Instantiate.recursive_application name qs args body in
              if dual then dual_type body else body
            in
            let r_unique_name = name ^ string_of_int !tygroup_ref.id in
            let r_linear () = StringMap.lookup name !tygroup_ref.linearity_map in
            ( ve,
              `RecursiveApplication
                { r_name = name; r_dual = false; r_unique_name; r_args; r_unwind; r_linear } ) )
    | Primitive k -> (ve, `Primitive k)
    | DB -> (ve, `Primitive Primitive.DB)
    | Input (t, s) ->
        let ve, t = datatype ve t in
        let ve, s = datatype ve s in
        (ve, `Input (t, s))
    | Output (t, s) ->
        let ve, t = datatype ve t in
        let ve, s = datatype ve s in
        (ve, `Output (t, s))
    | Select r ->
        let ve, r = row alias_env pos ve r in
        (ve, `Select r)
    | Choice r ->
        let ve, r = row alias_env pos ve r in
        (ve, `Choice r)
    | Dual s ->
        let ve, s = datatype ve s in
        (ve, `Dual s)
    | End -> (ve, `End)

  and fieldspec alias_env pos (ve : VarEnv.t) = function
    | Absent -> (ve, `Absent)
    | Present t ->
        let ve, t = datatype alias_env ve t in
        (ve, `Present t)
    | Var var ->
        let ve, var = VarEnv.lookup_pvar pos var ve in
        (ve, `Var var)

  and row alias_env pos (ve : VarEnv.t) (fields, rv) =
    let ve, seed =
      match rv with
      | Closed -> (ve, Types.make_empty_closed_row ())
      | Open var ->
          let ve, var = VarEnv.lookup_rvar pos var ve in
          (ve, (StringMap.empty, var, false))
      | Recursive (name, r) ->
          let vi, point, { VarEnv.var; _ } =
            VarEnv.add_var' (fun x -> `Row x) pos (name, None, `Flexible) ve
          in
          let vi, r = row alias_env pos vi r in
          let ve = VarEnv.close name ~inner:vi ~outer:ve in
          Unionfind.change point (`Recursive (var, r));
          (ve, (StringMap.empty, point, false))
    in
    let ve, fields =
      fold_map
        (fun ve (k, p) ->
          let vp, p = fieldspec alias_env pos ve p in
          (vp, (k, p)) )
        ve fields
    in
    (ve, fold_right Types.row_with fields seed)

  (** Closes any empty, open arrow rows on user-defined operations. Note any row which can be
      closed will have an unbound effect variable. *)
  and effect_row alias_env pos (ve : VarEnv.t) (fields, rv) =
    let fields =
      List.map
        (function
          | (name, Present { node = Function (domain, (fields, rv), codomain); pos }) as op
            when not (TypeUtils.is_builtin_effect name) -> (
            (* Elaborates `Op : a -> b' to `Op : a {}-> b' *)
            match (rv, fields) with
            | Closed, [] -> op
            | Open _, [] | Recursive _, [] ->
                (* might need an extra check on recursive rows *)
                (name, Present (WithPos.make ~pos (Function (domain, ([], Closed), codomain))))
            | _ ->
                Type_error
                  ( pos,
                    "The abstract operation " ^ name ^ " has unexpected "
                    ^ "effects in its signature. The effect signature on an "
                    ^ "abstract operation arrow is always supposed to be empty, "
                    ^ "since any effects it might have are ultimately conferred by its handler." )
                |> raise )
          | x -> x )
        fields
    in
    let ve, (fields, rho, dual) = row alias_env pos ve (fields, rv) in
    let fields =
      StringMap.mapi
        (fun name -> function
          | `Present t when not (TypeUtils.is_builtin_effect name || TypeUtils.is_function_type t)
            ->
              (* Elaborates `Op : a' to `Op : () {}-> a' *)
              let eff = Types.make_empty_closed_row () in
              `Present (Types.make_function_type [] eff t)
          | t -> t )
        fields
    in
    (ve, (fields, rho, dual))

  and type_arg alias_env pos (ve : VarEnv.t) = function
    | Type t ->
        let ve, t = datatype alias_env ve t in
        (ve, `Type t)
    | Row r ->
        let ve, r = row alias_env pos ve r in
        (ve, `Row r)
    | Presence f ->
        let ve, f = fieldspec alias_env pos ve f in
        (ve, `Presence f)

  and effect_type_arg alias_env pos (ve : VarEnv.t) = function
    | Row r ->
        let ve, r = effect_row alias_env pos ve r in
        (ve, `Row r)
    | t -> type_arg alias_env pos ve t

  (** Build up an initial quantifier set, ensuring qualified variables are not already captured,
      and there are no duplicates. *)
  and make_forall var_env pos (qs : Sugartypes.quantifier list) : VarEnv.t * Types.quantifier list
      =
    let ve, _, quants =
      List.fold_right
        (fun (name, (pk, sk), freedom) (ve, args, arg_list) ->
          if StringSet.mem name args then raise (duplicate_var pos name);
          let ve, ({ VarEnv.var; meta_var; _ } as def) =
            match pk with
            | PrimaryKind.Type -> VarEnv.add_def (fun x -> `Type x) pos (name, sk, freedom) ve
            | PrimaryKind.Row -> VarEnv.add_def (fun x -> `Row x) pos (name, sk, freedom) ve
            | PrimaryKind.Presence ->
                VarEnv.add_def (fun x -> `Presence x) pos (name, sk, freedom) ve
          in
          (ve, StringSet.add name args, (var, VarEnv.close_over def, meta_var) :: arg_list) )
        qs (var_env, StringSet.empty, [])
    in
    (ve, quants)

  and close_forall ~outer =
    List.fold_left (fun inner (name, _, _) -> VarEnv.close name ~inner ~outer)

  let datatype' alias_env ve ((dt, _) : datatype') =
    let vdt, t = datatype alias_env ve dt in
    (vdt, (dt, Some t))

  (** Desugar a table literal. No free variables are allowed here. We generate both read and write
      types by looking for readonly constraints *)
  let table_lit alias_env constraints dt =
    let { VarEnv.tyvars; _ }, read_type = datatype alias_env VarEnv.empty dt in
    StringMap.iter
      (fun _ { VarEnv.name; usage; _ } -> raise (free_type_variable usage name))
      tyvars;
    let write_row, needed_row =
      match TypeUtils.concrete_type read_type with
      | `Record (fields, _, _) ->
          StringMap.fold
            (fun label t (write, needed) ->
              match lookup label constraints with
              | Some cs ->
                  if List.exists (( = ) Readonly) cs then (write, needed)
                  else
                    (* if List.exists ((=) `Default) cs then *)
                    (Types.row_with (label, t) write, needed)
              | _ ->
                  let add = Types.row_with (label, t) in
                  (add write, add needed) )
            fields
            (Types.make_empty_closed_row (), Types.make_empty_closed_row ())
      | _ -> raise (internal_error "Table types must be record types")
    in
    (* We deliberately don't concretise the returned read_type in the hope of improving error
       messages during type inference. *)
    (read_type, `Record write_row, `Record needed_row)
end

let tygroup_counter = ref 0

let fresh_tygroup_id = function
  | () ->
      let ret = !tygroup_counter in
      tygroup_counter := ret + 1;
      ret

(** Convert a syntactic type into a semantic type *)
let desugar implicit_effect initial_alias_env =
  object (self)
    inherit SugarTraversals.fold_map as super

    val alias_env = initial_alias_env

    method aliases = alias_env

    val var_env = { VarEnv.empty with VarEnv.implicit_effect }

    method var_env = var_env

    method! datatype' dt =
      let var_env, dt = Desugar.datatype' alias_env var_env dt in
      ({<var_env>}, dt)

    method! phrasenode =
      function
      | Block (bs, p) ->
          (* aliases bound in `bs' should not escape the scope of the block *)
          let o, bs = self#list (fun o -> o#binding) bs in
          let o, p = o#phrase p in
          (* NB: we return `self' rather than `_o' in order to return to the outer scope; any
             aliases bound in _o are unreachable from outside the block *)
          ({<var_env = o#var_env>}, Block (bs, p))
      | TableLit (t, (dt, _), cs, keys, p) ->
          let read, write, needed = Desugar.table_lit alias_env cs dt in
          let o, t = self#phrase t in
          let o, keys = o#phrase keys in
          let o, p = o#phrase p in
          (o, TableLit (t, (dt, Some (read, write, needed)), cs, keys, p))
      | p -> super#phrasenode p

    method! bindingnode =
      function
      | Typenames ts ->
          (* Maps syntactic types in the recursive group to semantic types. *)
          (* This must be empty to start off with, because there's a cycle in calculating the
             semantic types: we need the alias environment populated with all types in the group in
             order to calculate a semantic type. We populate the reference in a later pass. *)
          let tygroup_ref =
            ref
              { id = fresh_tygroup_id ();
                type_map = StringMap.empty;
                linearity_map = StringMap.empty
              }
          in
          (* Each type will have its own variable environment, used in later passes.*)
          let venvs_map = StringMap.empty in
          (* Add all type declarations in the group to the alias environment, as mutuals.
             Quantifiers need to be desugared. *)
          let mutual_env, venvs_map =
            List.fold_left
              (fun (alias_env, venvs_map) (t, args, _, pos) ->
                let qs = List.map fst args in
                let var_env, qs = Desugar.make_forall VarEnv.empty pos qs in
                let venvs_map = StringMap.add t var_env venvs_map in
                (Env.String.bind alias_env (t, `Mutual (qs, tygroup_ref)), venvs_map) )
              (alias_env, venvs_map) ts
          in
          (* Desugar all DTs, given the temporary new alias environment. *)
          let desugared_mutuals =
            List.map
              (fun (name, args, dt, pos) ->
                let sugar_qs = List.map fst args in
                (* Semantic quantifiers have already been constructed, so retrieve them *)
                let sem_qs =
                  match Env.String.find mutual_env name with
                  | Some (`Mutual (qs, _)) -> qs
                  | _ -> assert false
                in
                let args =
                  ListUtils.zip' sugar_qs sem_qs |> List.map (fun (sq, q) -> (sq, Some q))
                in
                (* Desugar the datatype *)
                let var_env = StringMap.find name venvs_map in
                let var_env, dt' = Desugar.datatype' mutual_env var_env dt in
                (* Check if the datatype has actually been desugared *)
                let t, dt =
                  match dt' with
                  | t, Some dt -> (t, dt)
                  | _ -> assert false
                in
                let { VarEnv.tyvars; _ } = Desugar.close_forall ~outer:VarEnv.empty var_env sugar_qs in
                StringMap.iter
                  (fun _ { VarEnv.name; usage; _ } -> raise (free_type_variable usage name))
                  tyvars;
                (name, args, (t, Some dt), pos) )
              ts
          in
          (* Given the desugared datatypes, we now need to handle linearity. *)
          (* First, calculate linearity up to recursive application, and a
           * dependency graph. *)
          let linearity_env, dep_graph =
            List.fold_left
              (fun (lin_map, dep_graph) (name, _, (_, dt), _) ->
                let dt = OptionUtils.val_of dt in
                let lin_map = StringMap.add name (not @@ is_unl_type dt) lin_map in
                let deps = recursive_applications dt in
                let dep_graph = (name, deps) :: dep_graph in
                (lin_map, dep_graph) )
              (StringMap.empty, []) desugared_mutuals
          in
          (* Next, topo-sort the dependency graph. We need to reverse since we
           * propagate linearity information downwards from the SCCs which everything
           * depends on, rather than upwards. *)
          let sorted_graph = Graph.topo_sort_sccs dep_graph |> List.rev in
          (* Next, propagate the linearity information through the graph,
           in order to construct the final linearity map.
           * Given the topo-sorted dependency graph, we propagate linearity based
           * on the following rules:
           * 1. If any type in a SCC is linear, then all types in that SCC must
           *    also be linear.
           * 2. If a type depends on a linear type, then it must also be linear.
           * 3. Otherwise, the type is unrestricted.
           *
           * Given that we have a topo-sorted graph, as soon as we come across a
           * linear SCC, we know that the remaining types are also linear. *)
          let linearity_map, _ =
            List.fold_right
              (fun scc (acc, lin_found) ->
                let scc_linear =
                  lin_found || List.exists (fun x -> StringMap.find x linearity_env) scc
                in
                let acc = List.fold_left (fun acc x -> StringMap.add x scc_linear acc) acc scc in
                (acc, scc_linear) )
              sorted_graph (StringMap.empty, false)
          in
          (* Finally, construct a new alias environment, and populate the map from
           * strings to the desugared datatypes which in turn allows recursive type
           * unwinding in unification. *)
          (* NB: type aliases are scoped; we allow shadowing. We also allow type aliases to shadow
             abstract types. *)
          let alias_env =
            List.fold_left
              (fun alias_env (t, args, (_, dt'), _) ->
                let dt = OptionUtils.val_of dt' in
                let semantic_qs = List.map (snd ->- val_of) args in
                let alias_env =
                  Env.String.bind alias_env (t, `Alias (List.map (snd ->- val_of) args, dt))
                in
                tygroup_ref :=
                  { !tygroup_ref with
                    type_map = StringMap.add t (semantic_qs, dt) !tygroup_ref.type_map;
                    linearity_map
                  };
                alias_env )
              alias_env desugared_mutuals
          in
          ({<alias_env>}, Typenames desugared_mutuals)
      | Foreign (bind, raw_name, lang, file, dt) ->
          let _, bind = self#binder bind in
          let var_env, dt = Desugar.datatype' alias_env VarEnv.empty dt in
          VarEnv.close_all var_env;
          (self, Foreign (bind, raw_name, lang, file, dt))
      | b -> super#bindingnode b

    method recursive_function (bind, lin, (tyvars, fl), loc, dt, pos) =
      let o, bind = self#binder bind in
      let o, fl = o#funlit fl in
      let o, loc = o#location loc in
      let o, dt = o#option (fun x -> x#datatype') dt in
      let o, pos = o#position pos in
      (o, (bind, lin, (tyvars, fl), loc, dt, pos))

    method! sentence _ = failwith "Should never call #sentence"

    method! program _ = failwith "Should never call #program"
  end

let phrase alias_env p =
  let implicit =
    Settings.get_value Basicsettings.Types.effect_sugar && (all_anon_effects#phrase p)#satisfied
  in
  let o, p = (desugar implicit alias_env)#phrase p in
  VarEnv.close_all o#var_env; p

let binding alias_env ({ node; pos } as bind) =
  let eff_sugar = Settings.get_value Basicsettings.Types.effect_sugar in
  match node with
  | Funs bnds ->
      (* We visit each function binding separately, as it should have a distinct type variable
         environment on the toplevel. *)
      let bnds =
        List.map
          (fun bnd ->
            let eff_sugar = eff_sugar && (all_anon_effects#recursive_function bnd)#satisfied in
            let o, bnd = (desugar eff_sugar alias_env)#recursive_function bnd in
            VarEnv.close_all o#var_env; bnd )
          bnds
      in
      (alias_env, WithPos.make ~pos (Funs bnds))
  | _ ->
      let eff_sugar = eff_sugar && (all_anon_effects#binding bind)#satisfied in
      let o, bind = (desugar eff_sugar alias_env)#binding bind in
      VarEnv.close_all o#var_env; (o#aliases, bind)

let toplevel_bindings alias_env bs =
  let alias_env, bnds =
    List.fold_left
      (fun (alias_env, bnds) bnd ->
        let aliases, bnd = binding alias_env bnd in
        (aliases, bnd :: bnds) )
      (alias_env, []) bs
  in
  (alias_env, List.rev bnds)

let program typing_env ((bindings, p) : Sugartypes.program) : Sugartypes.program =
  let alias_env = typing_env.tycon_env in
  let alias_env, bindings = toplevel_bindings alias_env bindings in
  (* let typing_env = { typing_env with tycon_env = alias_env } in *)
  (bindings, opt_map (phrase alias_env) p)

let sentence typing_env = function
  | Definitions bs ->
      let _alias_env, bs' = toplevel_bindings typing_env.tycon_env bs in
      Definitions bs'
  | Expression p -> Expression (phrase typing_env.tycon_env p)
  | Directive d -> Directive d

let read ~aliases s =
  let dt, _ = parse_string ~in_context:(LinksLexer.fresh_context ()) datatype s in
  let { VarEnv.vars; _ }, dt = Desugar.datatype aliases VarEnv.empty dt in
  let vars =
    List.rev vars
    |> List.map (fun ({ VarEnv.var; meta_var; _ } as def) -> (var, VarEnv.close_over def, meta_var))
  in
  List.iter Generalise.rigidify_quantifier vars;
  Types.for_all (vars, dt)
