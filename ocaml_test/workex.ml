
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)
let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

let rec length2 l =
  match l with
  | [] -> 0
  | _ :: t -> 1 + length2 t;;

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

(* flag in data that returns bool/2;  returns true if no flag in data *)
let flag_in_data_b2 n f k s = 
  let r = flag_in_data n f k s in
  match r with
    |True -> false 
    |False -> true

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

(* flag at data that returns bool/2;  returns true if no flag at overlap *)
let flag_at_overlap_b2 n f k s =
  let r = flag_at_overlap n f k s in
  match r with
    |True -> false
    |False -> true

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

(************* Newly written helper functions ************)
let rec lb2_to_lb1 l =
  match l with
  | [] -> Nil 
  | [True] -> Cons(True,Nil)
  | [False] -> Cons(False,Nil)
  | x::xs -> Cons(x,lb2_to_lb1 xs)

let rec combinations n = 
  match n with
  | 0 -> [Nil]
  | n ->
    let rest = combinations (n - 1) in
    let comb_f = List.map (fun l -> Cons(False,l)) rest in
    let comb_t = List.map (fun l -> Cons(True,l)) rest in
    comb_t @ comb_f;; 

(* range(n) = 0 to n *)
let rec range n = 
  match n with 
  | O -> [O]
  | S x -> (range x) @ [S x] ;;

(* range1(n) = 1 to n-1 *)
let rec range1 n = 
  match n with 
  | O -> []
  (* | n1 -> [n1] *)
  | S n -> (range1 n) @ [n] ;;




let rec all_combinations n = 
  match n with
  (* | 0 -> [Cons(True,Cons(False,Nil))] *)
  | 1 -> [Cons(True,Nil);Cons(False,Nil)]
  | n ->
    let rest = all_combinations (n - 1) in
    let comb_n = combinations n in
    rest @ comb_n;; 

let myFilter (f,k,s) = 
  let r1 = range(length k) in
  let r2 = range1(length f) in
  let b1 = List.for_all (fun n -> flag_in_data_b2 n f k s) r1 in
  let b2 = List.for_all (fun n -> flag_at_overlap_b2 n f k s) r2 in
  b1 && b2

let crossProd l1 l2 =
  List.concat (List.map (fun e1 -> List.map (fun e2 -> (e1,e2)) l2) l1);;

 
(**************** Different ToString Functions ****************)
let b2_to_str b =
  match b with
  | true -> "T"
  | false -> "F"

let b1_to_str b =
  match b with
  | True -> "T"
  | False -> "F"

let rec bool_list_to_str bl  = 
  match bl with
  | Nil -> ""
  | Cons (x, l') -> Printf.sprintf "%s%s" (if x==True then "T" else "F") (bool_list_to_str l');;

let rec combinations_to_string comb = 
  match comb with
  | [] -> ""
  | [Nil] -> ""
  | x::xs ->
      Printf.sprintf "[%s]%s" (bool_list_to_str x) (combinations_to_string xs);;

let rec list_of_pairs_to_string lt =
  match lt with
  | [] -> ""
  | [(Nil,Nil)] -> ""
  | (a, b) :: rest ->
    Printf.sprintf "(%s, %s) %s " (bool_list_to_str a) (bool_list_to_str b) (list_of_pairs_to_string rest);;


(********** Main : Checking functions with parameters **********)
let l = [True; True; False; True];;
let y = lb2_to_lb1 l;;
(* Printf.eprintf "lb1 = %s\n" (bool_list_to_str y);; *)
(* --------------------------------------------------------------------------- *)
let l = all_combinations 3;;
(* Printf.eprintf "all combinations(%d) = %s\n" 3 (combinations_to_string l);; *)
(* --------------------------------------------------------------------------- *)
let f1 = lb2_to_lb1 [False;True;False];;
let k1 = lb2_to_lb1 [False;True];;
let s1 = True;;
let ret = myFilter (f1,k1,s1);;
(* Printf.eprintf "myfilter (f1,k1,s1) = %s\n" (b2_to_str ret);; *)
(* --------------------------------------------------------------------------- *)
Printf.eprintf "\n\n****** WORKING EXAMPLES ******\n";;
let s = True;;
Printf.eprintf "\nstuffing bit = %s\n" (b1_to_str s);;
let flags = combinations 5;;
Printf.eprintf "\n\nflags = %s\n" (combinations_to_string flags);;
let kers = all_combinations 4;;
Printf.eprintf "\n\nkernels = %s\n" (combinations_to_string kers);;
let cp = crossProd flags kers;;
Printf.eprintf "\n\nCrossprod = %s\n" (list_of_pairs_to_string cp);;
let wp = List.filter(fun (x,y) -> myFilter (x,y,s)) cp;;
Printf.eprintf "\n\nWorking examples = %s\n" (list_of_pairs_to_string wp);;
Printf.eprintf "\n\n# of Working examples = %d\n" (length2 wp);;

(* let f2 = lb2_to_lb1 [False;False;False;False];;
let k2 = lb2_to_lb1 [False;False];;
let s2 = True;; *)
(* let q = flag_at_overlap_b2 (S(S(O))) f2 k2 s2;;
Printf.eprintf "result = %s\n" (b2_to_str q);; *)
