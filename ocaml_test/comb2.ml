type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

let rec app_ll l m =
  match l with
  | Nil -> m
  | Cons(Nil,Nil) -> m
  | Cons (a, l1) -> Cons (a, (app_ll l1 m))

let rec combinations n = 
  match n with
  | 0 -> [Nil]
  | n ->
    let rest = combinations (n - 1) in
    let comb_f = List.map (fun l -> Cons(False,l)) rest in
    let comb_t = List.map (fun l -> Cons(True,l)) rest in
    comb_t @ comb_f;; 

let rec bools_to_str bl =
  match bl with 
  | [] -> ""
  | b::bs -> Printf.sprintf "%s%s" (if b then "T" else "F") (bools_to_str bs);;

let rec bools_to_str1 b  = 
match b with
| Nil -> ""
| Cons (x, l') -> Printf.sprintf "%s%s" (if x==True then "T" else "F") (bools_to_str1 l');;


let rec combinations_to_string comb = 
  match comb with
  | [] -> ""
  | [Nil] -> ""
  | x::xs ->
      Printf.sprintf "[%s]%s" (bools_to_str1 x) (combinations_to_string xs);;


let l = combinations 3;;
Printf.eprintf "combinations(%d) = %s\n" 3 (combinations_to_string l);;


