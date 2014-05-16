module type S = sig

  type (_, _) term_plug
  type _ atom_plug

  type c = Id_for_scripts.c

  val constrain :
    c atom_plug Formula.t -> unit

  val minimize :
    (c, int) term_plug -> unit

  val solve : unit -> Terminology.result

  val fresh_int_var :
    unit -> (c, int) term_plug

  val fresh_bool_var :
    unit -> c atom_plug Formula.t

  val ideref :
    (c, int) term_plug -> Core.Std.Int63.t option

  val bderef :
    c atom_plug Formula.t -> bool option

  val toi :
    int -> (c, int) term_plug

  val toi63 :
    Core.Std.Int63.t -> (c, int) term_plug

  val string_of_result : Terminology.result -> string

  val solve_print_result : unit -> unit

  val argv : string array

end
