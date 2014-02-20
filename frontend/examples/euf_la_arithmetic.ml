open Script ;;
open Core.Std ;;

let n =
  if not !Sys.interactive && Array.length argv >= 2 then
    int_of_string argv.(1)
  else
    20 ;;

let (+!) x y = ~free ;;

for i = 0 to (n - 1) do
  for j = 0 to (n - 1) do
    let i = toi i
    and j = toi j
    and s = toi ((i + j) % n) in
    constrain (~logic (i +! j = s))
  done
done ;;

let succ x = ~free ;;

for i = 0 to (n - 1) do
  let i = toi i
  and s = toi ((i + 1) % n) in
  constrain (~logic (succ i = s))
done ;;

let pred x = ~free ;;

for i = 0 to (n - 1) do
  let i = toi i
  and s = toi ((i - 1) % n) in
  constrain (~logic (pred i = s))
done ;;

let a = fresh_int_var () ;;

let b = fresh_int_var () ;;

constrain (~logic (0 <= a && a < toi n)) ;;

constrain (~logic (0 <= b && b < toi n)) ;;

let z = ~logic (pred (a +! succ b) +! (b +! (pred (a +! b)))) ;;

constrain (~logic (z < 0 || z >= toi n)) ;;

solve_print_result () ;;
