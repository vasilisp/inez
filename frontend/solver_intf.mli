module type S = sig

  open Terminology

  (** context *)
  type ctx
  
  val make_ctx: unit -> ctx

  type c

  (** assert constraint *)
  val assert_formula :
    ctx -> c Lang_abstract.A.t Formula.t -> unit

  val solve : ctx -> result

  val deref_int :
    ctx -> (c, int) Lang_ids.t -> Core.Std.Int63.t option

  val deref_bool :
    ctx -> (c, bool) Lang_ids.t -> bool option

  val write_bg_ctx : ctx -> string -> unit

end
