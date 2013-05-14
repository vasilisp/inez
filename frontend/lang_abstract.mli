(* atomic formulas *)

module rec A : sig

  type 'i t =
  | A_Bool  of  ('i, bool) M.t
  | A_Le    of  ('i, int) M.t
  | A_Eq    of  ('i, int) M.t

end

(* terms *)

and M : sig

  type ('i, _) t =
  | M_Bool  :  'i A.t Formula.t -> ('i, bool) t
  | M_Int   :  Core.Std.Int63.t -> ('i, int) t
  | M_Sum   :  ('i, int) t * ('i, int) t ->  ('i, int) t
  | M_Prod  :  Core.Std.Int63.t * ('i, int) t -> ('i, int) t
  | M_Ite   : 'i A.t Formula.t * ('i, int) t * ('i, int) t ->
    ('i, int) t
  | M_Var   :  ('i, 's) Lang_ids.t -> ('i, 's) t
  | M_App   :  ('i, 'r -> 's) t * ('i, 'r) t -> ('i, 's) t

  (* constants *)

  val zero : ('a, int) t
  val one : ('a, int) t

  (* conversions *)

  val of_int63 : Core.Std.Int63.t -> ('a, int) t

  (* type utilities *)

  val type_of_t :
    ('i, 's) t -> f:'i Lang_ids.t_arrow_type -> 's Lang_types.t

  (* infix operators *)

  include (Ops_sig.Int with type ('i, 's) t := ('i, 's) t
                       and type i := Core.Std.Int63.t)

end

(* boxed terms *)

module Box : Box_sig.T2 with type ('i, 's) b := ('i, 's) M.t

(* mostly infix operators; that's the module "logic in e" uses under
   the hood *)

module Ops :
  (Ops_sig.All
   with type ('i, 's) t := ('i, 's) M.t
   and type 'i a := 'i A.t
   and type 'a f := 'a Formula.t
   and type i := Core.Std.Int63.t)
