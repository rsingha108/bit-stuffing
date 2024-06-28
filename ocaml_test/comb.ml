let rec combinations n = 
  match n with
  | 0 -> [[]]
  | n ->
    let rest = combinations (n - 1) in
    let comb_f = List.map (fun l -> 0::l) rest in
    let comb_t = List.map (fun l -> 1::l) rest in
    comb_t @ comb_f;; 

combinations 3;;

(*Change this accordingly, app instead of @*)


(* let rec combinations_to_string = function
| [] -> ""
| x::xs ->
    let rec bools_to_str = function
      | [] -> ""
      | b::bs -> Printf.sprintf "%s%s" (if b then "T" else "F") (bools_to_str bs)
    in
    Printf.sprintf "[%s]%s" (bools_to_str x) (combinations_to_string xs) *)

(* let _ =
  let n = int_of_string Sys.argv.(1) in
  let combs = combinations n in
  Printf.eprintf "combinations(%d) = %s\n" n (combinations_to_string combs) *)

(* combinations 3;; *)

(* 
let size = 4 in
(* '1 lsl size' computes 2^size *)
for i = 0 to (1 lsl size) - 1 do
   (* from: is the least significant bit '1'? *)
   let b0 = 1 = ((i / 1) mod 2) in
   let b1 = 1 = ((i / 2) mod 2) in
   let b2 = 1 = ((i / 4) mod 2) in
   (* to: is the most significant bit '1'? *)
   let b3 = 1 = ((i / 8) mod 2) in
   (* do your thing *)
   Printf.printf (b0+b1+b2+b3)
done *)


(* recursive function *)
(* let rec f n = match n with 0 -> 0 | 1 -> 1 | x -> f (n-1) + f (n-2);;
f 9;; *)

