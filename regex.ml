(* Representation for a very limited subset of (OCaml) regular
   expressions. *)

type repeat = Star | Plus | Question
                 deriving (Show)
type regex = | Range of (char * char)
             | Simply of string
             | Any
             | Seq of regex list
             | Repeat of (repeat * regex)
                 deriving (Show)

let compile_ocaml : regex -> Str.regexp = 
  let group = Printf.sprintf "\\(:?%s\\)" 
    (* non-capturing grouping *)
  in
  let compile_repeat = function
    | Star -> "*"
    | Plus -> "+"
    | Question -> "?" in
  let rec compile = function
    | Range (f, t) -> Printf.sprintf "[%s-%s]" (Str.quote (String.make 1 f)) (Str.quote (String.make 1 t))
    | Simply s ->  group (Str.quote s)
    | Any -> "."
    | Seq rs -> group (List.fold_right (fun input output -> (compile input) ^ output) rs "")
    | Repeat (s, r) -> group (compile r ^ compile_repeat s)
  in fun s -> Str.regexp ("^" ^ compile s ^ "$")

let tests : (string * regex * string * bool) list = 
  [
    (let s = "some .*string$\" ++?" in
       "splicing", Simply s, s, true);
    
    "range 0", Range ('0', '9'), "3", true;
    "range 1", Range ('0', '9'), "0", true;
    "range 2", Range ('0', '9'), "9", true;
    "range 3", Range ('0', '9'), ".", false;
    "range 4", Range ('a', 'z'), "p", true;
    "range 5", Range ('A', 'Z'), "p", false;

    "star 0", Repeat (Star, Any), "23r2r3", true;
    "star 1", Repeat (Star, Any), "", true;
    "star 2", Repeat (Star, (Simply "abc")), "abc", true;
    "star 3", Repeat (Star, (Simply "abc")), "abcabc", true;
    "star 4", Repeat (Star, (Simply "abc")), "", true;
    "star 5", Repeat (Star, (Simply "abc")), "a", false;
    "star 6", Repeat (Star, (Simply "abc")), "abca", false;

    "plus 0", Repeat (Plus, Any), "23r2r3", true;
    "plus 1", Repeat (Plus, Any), "", false;
    "plus 2", Repeat (Plus, (Simply "abc")), "abc", true;
    "plus 3", Repeat (Plus, (Simply "abc")), "abcabc", true;
    "plus 4", Repeat (Plus, (Simply "abc")), "", false;
    "plus 5", Repeat (Plus, (Simply "abc")), "a", false;
    "plus 6", Repeat (Plus, (Simply "abc")), "abca", false;

    "nesting 0", Seq [Simply "A";
                      Repeat (Plus, Simply "B")], "ABBB", true;

    "nesting 1", Seq [Simply "A";
                      Repeat (Plus, Simply "B")], "ABAB", false;

    "nesting 2", Repeat (Plus, Seq [Simply "A";
                                    Simply "B"]), "ABAB", true;

    "nesting 3", Repeat (Plus, Seq [Simply "A";
                                    Simply "B"]), "ABBB", false;
  ]

let run_tests = List.iter
  (fun (n, r, s, b) ->
     if Str.string_match (compile_ocaml r) s 0 = b 
     then prerr_endline ("PASS: " ^ n)
     else prerr_endline ("FAIL: " ^ n))

