(* Name: Andreas Singer
   Email: azsinger@bu.edu
   Course: CS320 Spring 2020
   Assignment: Interpreter Part 3
*)

type stackVal =
  | B of bool   (* <true> | <false> *)
  | I of int
  | N of string 
  | S of string
  | FunClos of string * string * environment * (command list) (* Closure: function name, formal param, current environment, function body *)
  | IOClos of string * string * environment * (command list)  (* InOut function closure *)
  | U           (* <unit> *)
  | E           (* <error> *)
  
and command =
  | PushB of stackVal
  | PushI of stackVal 
  | PushN of stackVal
  | PushS of stackVal 
  | Push  of stackVal
  | Add | Sub | Mul | Div | Rem | Neg
  | Pop
  | Swap
  | Concat 
  | And | Or | Not | LessThan | Equal | If 
  | Bind 
  | Begin | End 
  | Fun of string * string * (command list)      (* function name, param name, function body *)
  | InOutFun of string * string * (command list)
  | Call
  | Return
  | Quit 

and environment = (string * stackVal) list list

let empty_env : environment = [[]]

(* Create a binding in current environment *)
let create_binding (name :string) (sv :stackVal) (env :environment) : environment =
  match env with
  | env1 :: envs -> ((name, sv) :: env1) :: envs
  | []           -> [[(name, sv)]]

(* Fetch a binding from current environment *)
let rec fetch_binding (name :string) (env :environment) : stackVal option = 
  match env with
  | ((name1, sv) :: tl_env) :: envs -> if name = name1 then Some sv else fetch_binding name (tl_env :: envs)
  | []  :: envs                     -> fetch_binding name envs
  | []                              -> None

(* Push an empty environment *)
let pushEnv (env :environment) : environment = [] :: env

(* Pop the top environment off of the rest *)
let popEnv (env :environment) : environment = 
  match env with
  | []        -> empty_env
  | _ :: envs -> envs



let empty_stk = [[]]

let pushStackval (sv :stackVal) (stk :stackVal list list) : stackVal list list =
  match stk with
  | []           -> [[sv]]
  | stk1 :: stks -> (sv :: stk1) :: stks
  
  
(* Run commands *)
let rec run (coms :command list) (curr_env :environment) (stks :stackVal list list) : environment * (stackVal list) =
  let fetch (sv :stackVal) : stackVal =
    match sv with
    | N n -> (match fetch_binding n curr_env with
              | Some v -> v
              | None   -> N n)
    | _   -> sv
  in 
  let err_run tl_coms = run tl_coms curr_env (pushStackval E stks)
  in 
  match (coms, stks) with
  | (Quit        ::     _         , stk :: _) -> (curr_env, stk)
  | (Return      ::     _         , stk :: _) -> (curr_env, stk)
  | ([]                           , stk :: _) -> (curr_env, stk)

  | (PushB (B b) :: tl_coms, _) -> run tl_coms curr_env (pushStackval (B b) stks)
  | (PushI (I i) :: tl_coms, _) -> run tl_coms curr_env (pushStackval (I i) stks)
  | (PushN (N n) :: tl_coms, _) -> run tl_coms curr_env (pushStackval (N n) stks)
  | (PushS (S s) :: tl_coms, _) -> run tl_coms curr_env (pushStackval (S s) stks)
  | (Push U      :: tl_coms, _) -> run tl_coms curr_env (pushStackval U stks)
  | (Push E      :: tl_coms, _) -> run tl_coms curr_env (pushStackval E stks)
  | (Add         :: tl_coms, (x :: y :: stk) :: tl_stks) -> (match (fetch x, fetch y) with
                                                             | (I x, I y) -> run tl_coms curr_env ((I (x + y) :: stk) :: tl_stks)
                                                             | _          -> err_run tl_coms)
  | (Sub         :: tl_coms, (x :: y :: stk) :: tl_stks) -> (match (fetch x, fetch y) with
                                                             | (I x, I y) -> run tl_coms curr_env ((I (x - y) :: stk) :: tl_stks)
                                                             | _          -> err_run tl_coms)
  | (Mul         :: tl_coms, (x :: y :: stk) :: tl_stks) -> (match (fetch x, fetch y) with
                                                             | (I x, I y) -> run tl_coms curr_env ((I (x * y) :: stk) :: tl_stks)
                                                             | _          -> err_run tl_coms)
  | (Div         :: tl_coms, (x :: y :: stk) :: tl_stks) -> (match (fetch x, fetch y) with
                                                             | (I i, I 0) -> err_run tl_coms
                                                             | (I x, I y) -> run tl_coms curr_env ((I (x / y) :: stk) :: tl_stks)
                                                             | _          -> err_run tl_coms)                                              
  | (Rem         :: tl_coms, (x :: y :: stk) :: tl_stks) -> (match (fetch x, fetch y) with
                                                             | (I x, I 0) -> err_run tl_coms 
                                                             | (I x, I y) -> run tl_coms curr_env ((I (x mod y) :: stk) :: tl_stks)
                                                             | _          -> err_run tl_coms)
  | (Neg         :: tl_coms     , (x :: stk) :: tl_stks) -> (match fetch x with
                                                             | I x -> run tl_coms curr_env ((I (-x) :: stk) :: tl_stks)
                                                             | _          -> err_run tl_coms)
  | (Pop         :: tl_coms     , (x :: stk) :: tl_stks) -> run tl_coms curr_env (stk :: tl_stks)
  | (Swap        :: tl_coms, (x :: y :: stk) :: tl_stks) -> run tl_coms curr_env ((y :: x :: stk) :: tl_stks)  

  (* PA5, Interpreter Part 2: *)
  | (Concat      :: tl_coms, (x :: y :: stk) :: tl_stks) -> (match (fetch x, fetch y) with
                                                          | (S x, S y) -> run tl_coms curr_env ((S (x ^ y) :: stk) :: tl_stks)
                                                          | _          -> err_run tl_coms)
  | (And     :: tl_coms, (x :: y :: stk) :: tl_stks) -> (match (fetch x, fetch y) with
                                                         | (B x, B y) -> run tl_coms curr_env ((B (x && y) :: stk) :: tl_stks)
                                                         | _          -> err_run tl_coms)
  | (Or      :: tl_coms, (x :: y :: stk) :: tl_stks) -> (match (fetch x, fetch y) with
                                                         | (B x, B y) -> run tl_coms curr_env ((B (x || y) :: stk) :: tl_stks)
                                                         | _          -> err_run tl_coms)  
  | (Not     :: tl_coms, (x :: stk) :: tl_stks) -> (match fetch x with
                                                    | B x -> run tl_coms curr_env ((B (not x) :: stk) :: tl_stks)
                                                    | _          -> err_run tl_coms)  
  | (Equal     :: tl_coms, (x :: y :: stk) :: tl_stks) -> (match (fetch x, fetch y) with
                                                           | (I x, I y) -> run tl_coms curr_env ((B (x = y) :: stk) :: tl_stks)
                                                           | _          -> err_run tl_coms)     
  | (LessThan  :: tl_coms, (x :: y :: stk) :: tl_stks) -> (match (fetch x, fetch y) with
                                                           | (I x, I y) -> run tl_coms curr_env ((B (x < y) :: stk) :: tl_stks)
                                                           | _          -> err_run tl_coms)       
  | (Bind         :: tl_coms, (name :: value :: stk) :: tl_stks) -> (match name with               
                                                                    | N n -> (match fetch value with
                                                                              | E -> err_run tl_coms
                                                                              | N _ -> err_run tl_coms
                                                                              | v -> run tl_coms (create_binding n v curr_env) ((U :: stk) :: tl_stks))
                                                                    | _   -> err_run tl_coms)
  | (If     :: tl_coms, (x :: y :: z :: stk) :: tl_stks) -> (match (x, y, fetch z) with
                                                            | (a, b, B c) -> if c 
                                                                             then run tl_coms curr_env ((b :: stk) :: tl_stks)
                                                                             else run tl_coms curr_env ((a :: stk) :: tl_stks)
                                                            | _           -> err_run tl_coms)
  | (Begin :: tl_coms, tl_stks                         ) -> run tl_coms (pushEnv curr_env) ([] :: tl_stks)  
  | (End   :: tl_coms, (x :: stk) :: tl_stks)            -> run tl_coms (popEnv curr_env) (pushStackval x tl_stks)
  
  (* PA6 Interpreter Part 3: *)
  | (Fun (fname, argname, fbody)  :: tl_coms, _)     -> let clo = FunClos (fname, argname, curr_env, fbody) in
                                                        run tl_coms (create_binding fname clo curr_env) (pushStackval U stks)
  | (InOutFun (fname, argname, fbody) :: tl_coms, _) -> let clo = IOClos (fname, argname, curr_env, fbody) in
                                                        run tl_coms (create_binding fname clo curr_env) (pushStackval U stks)
 
  | (Call        :: tl_coms, (arg :: name :: stk) :: tl_stks) -> (match (fetch name, fetch arg) with
                                                                    | (_, E) -> err_run tl_coms
                                                                    | (_, N _) -> err_run tl_coms
                                                                    | (FunClos (fname, argname, fenv, fbody), sv) -> let (result_env, (result :: _)) = 
                                                                                                                  run fbody (create_binding argname sv (create_binding fname (FunClos (fname, argname, fenv, fbody)) fenv)) empty_stk
                                                                                                                  in let res = match result with
                                                                                                                               | N n -> let Some sv = fetch_binding n result_env in sv
                                                                                                                               | sv  -> sv
                                                                                                                  in
                                                                                                                  run tl_coms curr_env ((res :: stk) :: tl_stks)
                                                                    | (IOClos (fname, argname, fenv, fbody), sv) -> let (N calledArg) = arg
                                                                                                                    in let (result_env, (result :: _)) = run fbody (create_binding argname sv (create_binding fname (IOClos (fname, argname, fenv, fbody)) fenv)) empty_stk
                                                                                                                    in let res = match result with
                                                                                                                                 | N n -> let Some sv = fetch_binding n result_env in sv
                                                                                                                                 | sv  -> sv 
                                                                                                                    in let Some value = fetch_binding argname result_env in if List.mem Return fbody then
                                                                                                                    run tl_coms (create_binding calledArg value curr_env) ((res :: stk) :: tl_stks) else
                                                                                                                    run tl_coms (create_binding calledArg value curr_env) (stk :: tl_stks)
                                                                    | _ -> err_run tl_coms
                                                                 )

  | (_           :: tl_coms              , _ ) -> err_run tl_coms                
                                                                             
(* explode string into a char list *)
let explode (s :string) : char list =
  let rec expl (i :int) (l :char list) =
    if i < 0
    then l 
    else expl (i - 1) (String.get s i :: l)
  in expl (String.length s - 1) []

(* turn a char list back into a string *)
let implode (l :char list) : string =
  String.concat "" (List.map (String.make 1) l)

(* Return true when character is a letter *)
let is_alpha (c :char) : bool =
  (Char.code 'a' <= Char.code c && Char.code c <= Char.code 'z') ||
  (Char.code 'A' <= Char.code c && Char.code c <= Char.code 'Z')

let is_digit (c :char) : bool =
  Char.code '0' <= Char.code c && Char.code c <= Char.code '9'


let rec take_while' (p :'a -> bool) (es :'a list) : ('a list) * ('a list) =
  match es with
  | [] -> ([],[])
  | x::xs -> if p x 
             then let (chars, rest) = take_while' p xs in (x :: chars, rest)
             else ([], es)

let take_while (p :char -> bool) (s :string) : string * string =
  let (echars, erest) = take_while' p (explode s)
  in (implode echars, implode erest)

let parse_int (s :string) : int option =
  match int_of_string s with
  | n           -> Some n
  | exception _ -> None

let parse_string (s :string) : string option =
  if String.length s > 1 && String.get s 0 = '"' && String.get s (String.length s - 1) = '"'
  then Some (String.sub s 1 (String.length s - 2)) (* Check this *)
  else None

let parse_name (s :string) : string option =
  if String.length s > 0 && (let c = (String.get s 0) in is_alpha c || c = '_')
  then Some s (* Check this *)
  else None

let parse_constant (s :string) : stackVal =
  let s' = String.trim s in
  match s' with
  | "<true>"  -> B true
  | "<false>" -> B false
  | "<unit>"  -> U 
  | _         -> match parse_int s' with
                 | Some i -> I i 
                 | None   -> match parse_string s' with
                             | Some s -> S s 
                             | None   -> match parse_name s' with
                                         | Some s -> N s 
                                         | None   -> E 

let parse_funname (s :string) : string * string =
  let (funname, argname) = take_while (fun c -> is_digit c || is_alpha c || c = '_') (String.trim s)
  in (funname, (String.trim argname))
  

let parse_single_command (s :string) : command =
  match take_while is_alpha (String.trim s) with
  | ("PushB"   , p) -> PushB (parse_constant p)
  | ("PushI"   , p) -> PushI (parse_constant p)
  | ("PushN"   , p) -> PushN (parse_constant p)
  | ("PushS"   , p) -> PushS (parse_constant p)
  | ("Push"    , p) -> Push (parse_constant p)
  | ("Add"     , _) -> Add
  | ("Sub"     , _) -> Sub
  | ("Mul"     , _) -> Mul
  | ("Div"     , _) -> Div
  | ("Rem"     , _) -> Rem
  | ("Neg"     , _) -> Neg
  | ("Pop"     , _) -> Pop
  | ("Swap"    , _) -> Swap
  | ("Concat"  , _) -> Concat
  | ("And"     , _) -> And
  | ("Or"      , _) -> Or
  | ("Not"     , _) -> Not
  | ("LessThan", _) -> LessThan
  | ("Equal"   , _) -> Equal
  | ("Bind"    , _) -> Bind
  | ("If"      , _) -> If
  | ("Begin"   , _) -> Begin
  | ("End"     , _) -> End 
  (* | ("Fun"     , p) -> let (n1, n2) = parse_funname p in Fun (n1, n2)
  | ("FunEnd"  , _) -> FunEnd *)
  | ("Call"    , _) -> Call
  | ("Return"  , _) -> Return 
  | ("Quit"    , _) -> Quit
  | (_         , _) -> Quit 

let rec parse_until_funend (ls :string list) : (command list) * (string list) =
  match ls with
  | []             -> ([], [])
  | "FunEnd" :: tl -> ([], tl)
  | hd :: tl       -> (match take_while is_alpha (String.trim hd) with
                       | ("Fun", names) -> let (fname, argname) = parse_funname names in
                                           let (fbody, tl_coms) = parse_until_funend tl in
                                           let func = Fun (fname, argname, fbody) in
                                           let (coms, tl_coms') = parse_until_funend tl_coms in
                                           (func :: coms, tl_coms')
                       | ("InOutFun", names) -> let (fname, argname) = parse_funname names in
                                                let (fbody, tl_coms) = parse_until_funend tl in
                                                let func = InOutFun (fname, argname, fbody) in
                                                let (coms, tl_coms') = parse_until_funend tl_coms in
                                                (func :: coms, tl_coms')
                       | _                   -> let com = parse_single_command hd in
                                                let (coms, tl_coms) = parse_until_funend tl in
                                                (com :: coms, tl_coms)
                      )


let rec parse_input (ls :string list) : (command list) =
  let (coms, _) = parse_until_funend ls in coms
  
let stackVal_to_string (s :stackVal) : string =
  match s with
  | B b -> "<" ^ string_of_bool b ^ ">"
  | I i -> string_of_int i 
  | N n -> n 
  | S s -> s
  | FunClos _ -> "<CLOSURE>"
  | IOClos  _ -> "<CLOSURE>"
  | U   -> "<unit>"
  | E   -> "<error>"

(* File IO functions *)
(* recursive readlines function from lab2 *)
let rec readlines (path : string) : string list =
  let rec loop (ch : in_channel) : string list =
    match input_line ch with 
    | str -> str :: loop ch
    | exception  End_of_file -> [] (* input_line throws an exception at the end of the file *)
  in 
  let ch    = open_in path in
  let lines = loop ch in
  let ()    = close_in ch in
  lines

(* recursive writelines function from lab2 *)
let rec writelines (path : string) (ls : string list) : unit =
  let rec loop (ch) (ls : string list ) : unit =
    match ls with
    | []      -> ()
	  | x :: xs -> let _ = Printf.fprintf ch "%s\n" x in loop ch xs
  in 
  let ch = open_out path in
  let ()  = loop ch ls in
  let () = close_out ch in
  ()


   

(* run the interperter on the commands in inputFile and write the resulting stackVal list list in outputFile *)
let interpreter (inputFile : string) (outputFile : string) : unit = 
  let lines_in = readlines (inputFile) in

  let commands = parse_input lines_in in
  let (env, stk) = run commands empty_env [] in
  let lines_out = List.map stackVal_to_string stk in

  writelines outputFile lines_out
  
