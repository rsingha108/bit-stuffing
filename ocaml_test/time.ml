let time f =
  let t = Sys.time() in
  let res = f () in
  Printf.printf "Execution time: %f seconds\n"
                (Sys.time() -. t);
  res
;;

let rec fib n = if n < 3 then 1 else fib (n-1) + fib (n-2);;

time (fun () -> fib 41);;