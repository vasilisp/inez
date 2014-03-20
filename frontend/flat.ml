open Core.Std

module M = struct

  type ('i, _) t =
  | M_Var  :  ('i, 's) Id.t ->
    ('i, 's) t
  | M_App  :  ('i, 'r -> 's) t * ('i, 'r) Id.t ->
    ('i, 's) t

  let rec fun_id_of_app :
  type r s . ('i, r) t ->  'i Id.Box_arrow.t option =
    function
    | M_App (M_Var id, _) ->
      Some (Id.Box_arrow.Box id)
    | M_App (f, _) ->
      fun_id_of_app f
    | _ ->
      None

  let rec type_of_t :
  type r s . ('i, s) t -> s Type.t =
    function
    | M_Var id ->
      Id.type_of_t id
    | M_App (f, id) ->
      let t_f = type_of_t f
      and t_id = Id.type_of_t id in
      Type.t_of_app t_f t_id

  let id_of_t = function
    | M_Var id ->
      Some id
    | _ ->
      None

end

include M

module Conv (M : Logic_intf.Term_with_ops) = struct

  type 'i binding =
  [ `Int   of  (('i, int) Id.t * ('i, int) M.t)
  | `Bool  of  (('i, bool) Id.t * ('i, bool) M.t)
  ]

  let term_of_id :
  type s . ('i, s) Id.t -> bindings:'i binding list -> ('i, s) M.t =
    fun id ~bindings ->
      match
        let f (b : 'i binding) =
          match b, Id.type_of_t id with
          | `Int (id', m), Type.Y_Int ->
            id' = id
          | `Bool (id', m), Type.Y_Bool ->
            id' = id
          | _, _ ->
            false in
        List.find bindings ~f
      with
      | Some (`Int (_, m)) ->
        (match Id.type_of_t id with
        | Type.Y_Int ->
          m
        | _ ->
          M.M_Var id)
      | Some (`Bool (_, m)) ->
        (match Id.type_of_t id with
        | Type.Y_Bool ->
          m
        | _ ->
          M.M_Var id)
      | None ->
        M.M_Var id

  let rec term_of_t :
  type s . ('i, s) t -> bindings:'i binding list -> ('i, s) M.t =
    fun m ~bindings ->
      match m with
      | M_Var v ->
        term_of_id v ~bindings
      | M_App (f, id) ->
        M.M_App (term_of_t f ~bindings, term_of_id id ~bindings)

end

module Matching (M : Logic_intf.Term_with_ops) = struct

  type 'i binding =
  [ `Int   of  (('i, int) Id.t * ('i, int) M.t)
  | `Bool  of  (('i, bool) Id.t * ('i, bool) M.t)
  ]

  let equal_type :
  type r s . r Type.t -> s  Type.t -> bool =
    fun r s -> Type.Box.(compare (Box r) (Box s)) = 0

  let bind_id :
  type r s . ('i, s) M.t ->
    pattern:('i, r) Id.t -> 
    'i binding option =
    fun  m ~pattern ->
      match Id.type_of_t pattern, M.type_of_t m with
      | Type.Y_Int, Type.Y_Int ->
        Some (`Int (pattern, m))
      | Type.Y_Bool, Type.Y_Bool ->
        Some (`Bool (pattern, m))
      | _ ->
        None

  let rec bind_app :
  type r s .
  ?acc : 'i binding list ->
    ('i, s) M.t ->    
    pattern : ('i, r) t ->
    'i binding list option =
    fun ?acc:(acc = []) m ~pattern ->
      match pattern, m with
      | M_Var id, M.M_Var id' ->
        Option.some_if
          (compare (Id.Box.Box id) (Id.Box.Box id') = 0)
          (List.rev acc)
      | M_App (pattern, pattern_b), M.M_App (a', b') ->
        let f b =
          let acc = b :: acc in
          bind_app a' ~pattern ~acc in
        Option.(bind_id b' ~pattern:pattern_b >>= f)
      | _, _ ->
        None

  let rec do_for_match :
  type r s . ('i, r) M.t ->
    pattern  :  ('i, s) t ->
    f        :  ('i binding list -> unit) ->
    unit =
    fun m ~pattern ~f ->
      match pattern, m with
      | M_Var id, _ ->
        (match Id.type_of_t id, M.type_of_t m with
        | Type.Y_Int, Type.Y_Int ->
          f [`Int (id, m)]
        | Type.Y_Bool, Type.Y_Bool ->
          f [`Bool (id, m)]
        | _, _ ->
          raise (Unreachable.Exn _here_))
      | M_App (_, _), (M.M_App (a, b) as m) ->
        Option.iter (bind_app m ~pattern) ~f
      | _, _ ->
        ()

end

module Box = struct
  type 'i t = Box : ('i, 'r) M.t -> 'i t
end

module Box_arrow = struct
  type 'i t = Box : ('i, 'r -> 's) M.t -> 'i t
end
