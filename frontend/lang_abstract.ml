open Core.Std
open Terminology

module rec M :

  (Lang_abstract_intf.Term_with_ops with type 'i a := 'i A.t) =

struct

  type ('i, 'q) t =
  | M_Bool  :  'i A.t Formula.t -> ('i, bool) t
  | M_Int   :  Core.Std.Int63.t -> ('i, int) t
  | M_Sum   :  ('i, int) t * ('i, int) t ->  ('i, int) t
  | M_Prod  :  Core.Std.Int63.t * ('i, int) t -> ('i, int) t
  | M_Ite   :  'i A.t Formula.t * ('i, int) t * ('i, int) t ->
    ('i, int) t
  | M_Var   :  ('i, 's) Lang_ids.t -> ('i, 's) t
  | M_App   :  ('i, 'r -> 's) t * ('i, 'r) t -> ('i, 's) t

  let zero = M_Int Int63.zero

  let one = M_Int Int63.one

  let of_int63 x = M_Int x

  let rec type_of_t :
  type s . ('i, s) t -> f:('i Lang_ids.t_arrow_type) ->
    s Lang_types.t =
    fun x ~f:({Lang_ids.a_f} as f) ->
      match x with
      | M_Bool _ ->
        Lang_types.Y_Bool
      | M_Int _ ->
        Lang_types.Y_Int
      | M_Sum (_, _) ->
        Lang_types.Y_Int
      | M_Prod (_, _) ->
        Lang_types.Y_Int
      | M_Ite (_, _, _) ->
        Lang_types.Y_Int
      | M_Var id ->
        a_f id
      | M_App (a, b) ->
        let t_a = type_of_t a ~f
        and t_b = type_of_t b ~f in
        Lang_types.t_of_app t_a t_b

  let ( + ) a b =
    match a, b with
    | M_Int x, M_Int y ->
      M_Int Int63.(x + y)
    | M_Int x, _ when x = Int63.zero ->
      b
    | _, M_Int x when x = Int63.zero ->
      a
    | _ ->
      M_Sum (a, b)

  let ( * ) c a =
    if c = Int63.zero then
      M_Int Int63.zero
    else
      M_Prod (c, a)

  let ( - ) a b =
    match a, b with
    | M_Int x, M_Int y ->
      M_Int (Int63.(-) x y)
    | M_Int x, _ when x = Int63.zero ->
      Int63.minus_one * b
    | _, M_Int x when x = Int63.zero ->
      a
    | _ ->
      a + (Int63.minus_one * b)

end

and A : (Lang_abstract_intf.Atom
         with type ('i, 's) m := ('i, 's) M.t) = A

(* boxed terms *)

module Box = struct
  type 'i t = Box : ('i, _) M.t -> 'i t
end

module Ops = struct

  type 'a formula = 'a Formula.t

  include (M : Ops_intf.Int
           with type ('i, 'q) t := ('i, 'q) M.t
           and type i := Int63.t)

  include A

  include (Formula : Ops_intf.Prop
           with type 'a t := 'a formula)

  let iite c a b = M.M_Ite (c, a, b)

  let (<) a b =
    Formula.F_Atom (A_Le (M.(a + M_Int Int63.one - b)))

  let (<=) a b =
    Formula.F_Atom (A_Le M.(a - b))

  let (==) a b =
    Formula.F_Atom (A_Eq M.(a - b))

  let (>=) a b = b <= a

  let (>) a b = b < a

end
