(* this is bool1; bool2 is the default one *)
type bool =
| True
| False

type nat =
| O
| S of nat

(* this is list1, lis2 is the default list *)
type 'a list =
| Nil
| Cons of 'a * 'a list

(* To initialize a list1 : see the notation below *)

(* True/False : bool1 ; true/false : bool2*)
let x = Cons(True, Nil) ;; (*equivalent to [True]*)

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  match b1 with
  | True -> b2
  | False -> (match b2 with
              | True -> False
              | False -> True)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| Nil -> Nil
| Cons (x, l') -> app (rev l') (Cons (x, Nil))

(** val firstn : nat -> 'a1 list -> 'a1 list **)

let rec firstn n l =
  match n with
  | O -> Nil
  | S n0 ->
    (match l with
     | Nil -> Nil
     | Cons (a, l0) -> Cons (a, (firstn n0 l0)))

(** val skipn : nat -> 'a1 list -> 'a1 list **)

let rec skipn n l =
  match n with
  | O -> l
  | S n0 -> (match l with
             | Nil -> Nil
             | Cons (_, l0) -> skipn n0 l0)

(** val starts_with : bool list -> bool list -> bool **)

let rec starts_with a k =
  match a with
  | Nil -> (match k with
            | Nil -> True
            | Cons (_, _) -> False)
  | Cons (ha, ta) ->
    (match k with
     | Nil -> True
     | Cons (hk, tk) ->
       (match eqb ha hk with
        | True -> starts_with ta tk
        | False -> False))

(** val list_eq : bool list -> bool list -> bool **)

let rec list_eq a b =
  match a with
  | Nil -> (match b with
            | Nil -> True
            | Cons (_, _) -> False)
  | Cons (ha, ta) ->
    (match b with
     | Nil -> False
     | Cons (hb, tb) ->
       (match eqb ha hb with
        | True -> list_eq ta tb
        | False -> False))

(** val lastn : nat -> bool list -> bool list **)

let lastn n a =
  rev (firstn n (rev a))

(** val stuff : bool list -> bool list -> bool -> bool list **)

let rec stuff a k s =
  match a with
  | Nil -> Nil
  | Cons (ha, ta) ->
    (match starts_with (Cons (ha, ta)) k with
     | True ->
       app k (Cons (s, (stuff (skipn (length k) (Cons (ha, ta))) k s)))
     | False -> Cons (ha, (stuff ta k s)))

(** val destuff : bool list -> bool list -> bool list **)

let rec destuff a k =
  match a with
  | Nil -> Nil
  | Cons (ha, ta) ->
    (match starts_with (Cons (ha, ta)) k with
     | True ->
       app k (destuff (skipn (add (length k) (S O)) (Cons (ha, ta))) k)
     | False -> Cons (ha, (destuff ta k)))

(** val valid_message_start : bool list -> bool list -> bool -> bool **)

let rec valid_message_start a k s =
  match a with
  | Nil -> True
  | Cons (ha, ta) ->
    (match starts_with (Cons (ha, ta)) k with
     | True ->
       (match skipn (length k) (Cons (ha, ta)) with
        | Nil -> True
        | Cons (hs, ts) ->
          (match eqb hs s with
           | True -> valid_message_start ts k s
           | False -> False))
     | False -> valid_message_start ta k s)

(** val valid_message_start_and_end :
    bool list -> bool list -> bool -> bool **)

let rec valid_message_start_and_end a k s =
  match a with
  | Nil -> True
  | Cons (ha, ta) ->
    (match starts_with (Cons (ha, ta)) k with
     | True ->
       (match skipn (length k) (Cons (ha, ta)) with
        | Nil -> False
        | Cons (hs, ts) ->
          (match eqb hs s with
           | True -> valid_message_start_and_end ts k s
           | False -> False))
     | False -> valid_message_start_and_end ta k s)

(** val flag_in_data : nat -> bool list -> bool list -> bool -> bool **)

let rec flag_in_data n f k s =
  match n with
  | O -> valid_message_start f k s
  | S n' ->
    (match valid_message_start (app (firstn n k) f) k s with
     | True -> True
     | False -> flag_in_data n' f k s)

(** val valid_message_end : nat -> bool list -> bool list -> bool -> bool **)

let rec valid_message_end n a k s =
  match n with
  | O -> valid_message_start_and_end a k s
  | S n' ->
    (match valid_message_start_and_end (app (firstn n k) a) k s with
     | True -> True
     | False -> valid_message_end n' a k s)

(** val flag_at_overlap : nat -> bool list -> bool list -> bool -> bool **)

let rec flag_at_overlap n f k s =
  match n with
  | O -> False
  | S n' ->
    (match match list_eq (firstn n f) (lastn n f) with
           | True ->
             valid_message_end (length k) (firstn (sub (length f) n) f) k s
           | False -> False with
     | True -> True
     | False -> flag_at_overlap n' f k s)

(** val add_flags : bool list -> bool list -> bool list **)

let add_flags a f =
  app f (app a f)

(** val rem_end_flag : bool list -> bool list -> bool list **)

let rec rem_end_flag a f =
  match a with
  | Nil -> Nil
  | Cons (ha, ta) ->
    (match starts_with a f with
     | True -> Nil
     | False -> Cons (ha, (rem_end_flag ta f)))

(** val rem_flags : bool list -> bool list -> bool list **)

let rem_flags a f =
  match starts_with a f with
  | True -> rem_end_flag (skipn (length f) a) f
  | False -> Nil

  let rec rev = function
  | Nil -> Nil
  | Cons (x, l') -> app (rev l') (Cons (x, Nil))

let rec bools_to_str b  = 
  match b with
  | Nil -> ""
  | Cons (x, l') -> Printf.sprintf "%s%s" (if x==True then "T" else "F") (bools_to_str l');;
  
(* ============================ Random Bool Generator ================================= *)

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

(* ========================== Measure Performance ========================== *)

let n_iterations = 1000;;
let dataSize = 512;;

(* Generate a random bool list of length 12000 *)
let bool_list = random_bool_list dataSize;;
let a = bool_list;;

let f  = Cons(False,Cons(True,Cons(True,Cons(True,Cons(True,Cons(True,Cons(True,Cons(False, Nil))))))));;
let k = Cons(True,Cons(True,Cons(True,Cons(True,Cons(True,Nil)))));;
let s = False;;

let t1 = Sys.time();;

for i = 1 to n_iterations do
  let b = stuff a k s in
  let b1 = add_flags b f in
  let b2 = rem_flags b1 f in
  destuff b2 k
done

let t2 = Sys.time();;
let t = (t2 -. t1) *. 1000.0 ;;
let b = stuff a k s;;

Printf.printf "time taken in milliseconds =  %f\n"  t;;
