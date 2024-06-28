let rec combinations n = 
  match n with
  | 0 -> [[]]
  | n ->
    let rest = combinations (n - 1) in
    let comb_f = List.map (fun l -> false::l) rest in
    let comb_t = List.map (fun l -> true::l) rest in
    comb_t @ comb_f;; 

let rec bools_to_str bl =
  match bl with 
  | [] -> ""
  | b::bs -> Printf.sprintf "%s%s" (if b then "T" else "F") (bools_to_str bs);;

bools_to_str [true; false; true];;

let rec combinations_to_string comb = 
  match comb with
  | [] -> ""
  | x::xs ->
      Printf.sprintf "[%s]%s" (bools_to_str x) (combinations_to_string xs);;

combinations_to_string [[true;false];[false;true]];;

let l = combinations 3;;
Printf.eprintf "combinations(%d) = %s\n" 3 (combinations_to_string l);;

