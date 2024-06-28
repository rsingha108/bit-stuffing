(* This is bool1; bool2 is the default one *)
type bool =
| True
| False

type 'a list =
| Nil
| Cons of 'a * 'a list

(* Function to convert an OCaml bool to custom bool *)
let ocaml_bool_to_custom_bool = function
  | true -> True
  | false -> False

(* Function to generate a random bool *)
let random_bool () =
  Random.bool () |> ocaml_bool_to_custom_bool

(* Function to generate a random bool list of a given length *)
let rec random_bool_list length =
  if length <= 0 then Nil
  else Cons(random_bool (), random_bool_list (length - 1))

(* Initialize the random number generator *)
let () = Random.self_init ()

(* Generate a random bool list of length 12000 *)
let bool_list_12000 = random_bool_list 12000

(* Function to print a custom bool list *)
let rec print_custom_bool_list = function
  | Nil -> ()
  | Cons (True, t) -> print_string "True "; print_custom_bool_list t
  | Cons (False, t) -> print_string "False "; print_custom_bool_list t

(* Print the generated bool list *)
let () =
  Printf.printf "Random bool list of length 12000:\n";
  print_custom_bool_list bool_list_12000;
  Printf.printf "\n"
