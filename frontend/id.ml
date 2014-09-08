open Core.Std

module Id_untyped = (Int63 : Id_intf.Full_untyped)

module M = struct

  type ('c, 'u) t = Id_untyped.t * 'u Type.t

  let type_of_t = Tuple2.get2

  let sexp_of_t _ f x =
    Tuple2.sexp_of_t Id_untyped.sexp_of_t (Type.sexp_of_t f) x

  let compare _ _ (id1, _) (id2, _) =
    Id_untyped.compare id1 id2

  let is_int :
  type u . ('c, u) t -> bool =
    function
    | (_, Type.Y_Int) ->
      true
    | _ ->
      false

  let is_bool :
  type u . ('c, u) t -> bool =
    function
    | (_, Type.Y_Bool) ->
      true
    | _ ->
      false

end

include M

type ('c1, 'c2) id_mapper = {
  f_id : 's . ('c1, 's) t -> ('c2, 's) t
}

module Box = struct

  type 'c t = Box : ('c, _) M.t -> 'c t

  let compare _ x y =
    Pervasives.compare x y

  let sexp_of_t f (Box x) =
    let g _ = Sexplib.Sexp.Atom "" in
    let x = sexp_of_t f g x in
    Sexplib.Sexp.(List [Atom "Box"; x])

end

module Box_arrow = struct

  type 'c t = Box : ('c, _ -> _) M.t -> 'c t

  let compare _ x y =
    Pervasives.compare x y

  let sexp_of_t f (Box x) =
    let g _ = Sexplib.Sexp.Atom "" in
    let x = sexp_of_t f g x in
    Sexplib.Sexp.(List [Atom "Box"; x])

end

module type Generators =
  Id_intf.Generators with type ('c, 'u) t_plug := ('c, 'u) t

module type Accessors =
  Id_intf.Accessors with type ('c, 'u) t_plug := ('c, 'u) t

module type S =
  Id_intf.S with type ('c, 'u) t_plug := ('c, 'u) t

module Make () : S = struct

  (* [c] is empty. [c] is abstract outside this module. Applying the
     functor produces a different [c] each time. We tag IDs and
     expressions with [c], so that expressions with IDs that come from
     different contexts cannot be mixed. *)
  type c

  (* FIXME : clean up (i.e., do not raise exceptions) and put this in
     lang_types *)
  module TypeBox = struct
    module T = struct
      include Type.Box
      let t_of_sexp _ = raise (Unreachable.Exn _here_)
      let hash = Hashtbl.hash
    end
    include T
    include Hashable.Make(T)
  end

  let m = TypeBox.Table.create () ~size:64

  let update_id = Option.map ~f:Id_untyped.succ

  let gen_id :
  type u . u Type.t -> (c, u) t =
    fun x ->
      let x' = TypeBox.Box x in
      match Hashtbl.find m x' with
      | Some id ->
        Hashtbl.change m x' update_id; id, x
      | None ->
        let id = Id_untyped.succ Id_untyped.zero in
        Hashtbl.replace m x' id; Id_untyped.zero, x

  let type_of_t = type_of_t

  let compare_c _ _ = 0

  let sexp_of_c _ = Unit.sexp_of_t ()

end

module Make_mapper (I1 : S) (I2 : S) = struct

  let hashable_box = {
    Hashtbl.Hashable.
    hash = Hashtbl.hash;
    compare = Box.compare I1.compare_c;
    sexp_of_t = Box.sexp_of_t I1.sexp_of_c
  }

  let m = Hashtbl.create () ~size:20480 ~hashable:hashable_box

  let f : (I1.c, 'u) t -> (I2.c, 'u) t =
    fun ((_, y) as id) ->
      Hashtbl.find_or_add m (Box.Box id)
        ~default:(fun () -> Tuple2.get1 (I2.gen_id y)),
      y

  let f' = {f_id = f}
    
end
