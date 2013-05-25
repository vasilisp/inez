(* We build upon Solver to provide a solver for SMT-LIB
   instances. Smtlib_parser does the bulk of the translation. *)

module R : sig

  type 'r t = P_Ok of 'r | P_Unsupported | P_Syntax | P_Type | P_Bug

  val map : 'a t -> f:('a -> 'a) -> 'a t
  val map' : 'a t -> f:('a -> 'a t) -> 'a t

end

module Make
  
  (S : Solver_intf.S_unit_creatable)
  (I : Lang_ids.S with type c = S.c) :

sig

  (* All we are currently exporting is the following function. It
     parses a channel containing a sequence of SMT-LIB commands and
     executes f on the result of each command. *)

  val main :
    in_channel ->
    f:(Terminology.result option R.t -> unit) ->
    f_err:(unit -> unit) ->
    unit

end
