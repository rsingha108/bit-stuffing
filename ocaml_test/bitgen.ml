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

(* Function to generate a custom bool list from an integer with a specified number of bits *)
let rec int_to_custom_bool_list n bits =
  if bits = 0 then Nil
  else 
    let bit = ocaml_bool_to_custom_bool ((n land 1) = 1) in
    Cons(bit, int_to_custom_bool_list (n lsr 1) (bits - 1))

(* Initialize the random number generator *)
let () = Random.self_init ()

(* Generate random 16-bit, 32-bit, and 64-bit numbers *)
let random_16_bit = Random.int (1 lsl 16)  (* 16-bit random number *)
let random_32_bit = Int32.to_int (Random.int32 Int32.max_int)  (* 32-bit random number *)
let random_64_bit = Int64.to_int (Random.int64 Int64.max_int)  (* 64-bit random number *)

(* Convert the random numbers to custom bool lists *)
let bool_list_16 = int_to_custom_bool_list random_16_bit 16
let bool_list_32 = int_to_custom_bool_list random_32_bit 32
let bool_list_64 = int_to_custom_bool_list random_64_bit 64

(* Function to print a custom bool list *)
let rec print_custom_bool_list = function
  | Nil -> ()
  | Cons (True, t) -> print_string "True "; print_custom_bool_list t
  | Cons (False, t) -> print_string "False "; print_custom_bool_list t

(* Print the custom bool lists *)
let () =
  Printf.printf "Random 16-bit number as custom bool list: ";
  print_custom_bool_list bool_list_16;
  Printf.printf "\nRandom 32-bit number as custom bool list: ";
  print_custom_bool_list bool_list_32;
  Printf.printf "\nRandom 64-bit number as custom bool list: ";
  print_custom_bool_list bool_list_64;
  Printf.printf "\n"
