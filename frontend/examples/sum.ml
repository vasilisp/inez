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

let a = fresh_int_var () ;;

let b = fresh_int_var () ;;

constrain (~logic (0 <= a && a < toi n)) ;;

constrain (~logic (0 <= b && b < toi n)) ;;

constrain (~logic (a +! b >= toi n)) ;;

solve_print_result () ;;
