open Core.Std

module Id = (Int63 : Id_intf.Full)

type ('c, 't) t = Id.t

module Make (U : Unit.S) = struct

  type c

  type box = Box : _ Lang_types.t -> box

  let m = Hashtbl.Poly.create () ~size:1024

  let conv : type u . Id.t -> (c, u) t = Fn.id

  let get_fresh_id :
  type u . u Lang_types.t -> (c, u) t =
    fun x ->
      let x = Box x in
      match Hashtbl.find m x with
      | Some id ->
        Hashtbl.change m x (Option.map ~f:Id.succ);
        (* without conv, the compiler complains that u would escape
           its scope; no clue why *)
        conv id
      | None ->
        Hashtbl.replace m x (Id.succ Id.zero); Id.zero

end

module type S = sig
  type c
  val get_fresh_id  : 'u Lang_types.t -> (c, 'u) t
end
