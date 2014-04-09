open Core.Std

module M = struct

  type ('i, _) t =
  | M_Var  :  ('i, 's) Id.t ->
    ('i, 's) t
  | M_App  :  ('i, 'r -> 's) t * ('i, 'r) Id.t ->
    ('i, 's) t

  type 'i binding =
  [ `Int   of  ('i, int) Id.t * ('i, int) t
  | `Bool  of  ('i, bool) Id.t * ('i, bool) t
  ]

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

module Conv

  (I : Id.S)
  (E : Logic_intf.Term_with_ops) =

struct

  type c = I.c

  type binding =
  [ `Int   of  (c, int) Id.t * (c, int) E.t
  | `Bool  of  (c, bool) Id.t * (c, bool) E.t
  ]
  
  type rev_binding = (c, int) Id.t * (c, int) t Terminology.iexpr

  let term_of_id :
  type s . (c, s) Id.t -> bindings:binding list -> (c, s) E.t =
    fun id ~bindings ->
      match
        let f (b : binding) =
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
          E.M_Var id)
      | Some (`Bool (_, m)) ->
        (match Id.type_of_t id with
        | Type.Y_Bool ->
          m
        | _ ->
          E.M_Var id)
      | None ->
        E.M_Var id

  let rec term_of_t :
  type s . (c, s) t -> bindings:binding list -> (c, s) E.t =
    fun m ~bindings ->
      match m with
      | M_Var v ->
        term_of_id v ~bindings
      | M_App (f, id) ->
        E.M_App (term_of_t f ~bindings, term_of_id id ~bindings)

  let rec sum_of_term m ~bindings =
    let open Option in
    let f acc c m =
      acc >>= (fun (l, bindings) ->
        t_of_term m ~bindings >>| (fun (m, bindings) ->
          (c, m) :: l, bindings))
    and f_offset acc o =
      acc >>| (fun (l, bindings) -> (l, o), bindings)
    and init = Some ([], bindings)
    and factor = Int63.one in
    E.fold_sum_terms m ~init ~factor ~f ~f_offset

  and t_of_sum_term m ~bindings =
    let open Option in
    sum_of_term m ~bindings >>| (function
    | ([one, m], zero), bindings
      when one = Int63.one && zero = Int63.zero ->
      m, bindings
    | (l, o), bindings ->
      Printf.printf "definition for list\n%!";
      let id = I.gen_id Type.Y_Int in
      M_Var id, (id, (l, o)) :: bindings)

  and t_of_term :
  type s . (c, s) E.t ->
    bindings : rev_binding list ->
    ((c, s) t * rev_binding list) option =
    fun m ~bindings ->
      match m with
      | E.M_Bool _ ->
        None
      | E.M_Int i ->
        let id = I.gen_id Type.Y_Int in
        Some (M_Var id, (id, ([], i)) :: bindings)
      | E.M_Sum (_, _) ->
        t_of_sum_term m ~bindings
      | E.M_Prod (_, _) ->
        t_of_sum_term m ~bindings
      | E.M_Var id ->
        Some (M_Var id, bindings)
      | E.M_Ite (_, _, _) ->
        None
      | E.M_App (a, b) ->
        (match E.type_of_t b with
        | Type.Y_Int ->
          let open Option in
          t_of_term a ~bindings >>= (fun (a, bindings) ->
            t_of_term b ~bindings >>= (function
            | M_Var id, bindings ->
              Some (M_App (a, id), bindings)
            | b, bindings ->
              (match type_of_t b with
              | Type.Y_Int ->
                let id = I.gen_id Type.Y_Int in
                Some (M_App (a, id),
                      (id, Int63.([one, b], zero)) :: bindings)
              | _ ->
                None)))
        | _ ->
          None)

end

module Matching (E : Logic_intf.Term_with_ops) = struct

  type 'i binding =
  [ `Int   of  (('i, int) Id.t * ('i, int) E.t)
  | `Bool  of  (('i, bool) Id.t * ('i, bool) E.t)
  ]

  let equal_type :
  type r s . r Type.t -> s  Type.t -> bool =
    fun r s -> Type.Box.(compare (Box r) (Box s)) = 0

  let bind_id :
  type r s . ('i, s) E.t ->
    pattern:('i, r) Id.t -> 
    'i binding option =
    fun  m ~pattern ->
      match Id.type_of_t pattern, E.type_of_t m with
      | Type.Y_Int, Type.Y_Int ->
        Some (`Int (pattern, m))
      | Type.Y_Bool, Type.Y_Bool ->
        Some (`Bool (pattern, m))
      | _ ->
        None

  let rec bind_app :
  type r s .
  ?acc : 'i binding list ->
    ('i, s) E.t ->    
    pattern : ('i, r) t ->
    'i binding list option =
    fun ?acc:(acc = []) m ~pattern ->
      match pattern, m with
      | M_Var id, E.M_Var id' ->
        if compare (Id.Box.Box id) (Id.Box.Box id') = 0 then
          Some (List.rev acc)
        else
          None
      | M_App (pattern, pattern_b), E.M_App (a', b') ->
        let open Option in
        (bind_id b' ~pattern:pattern_b) >>= (fun b ->
          let acc = b :: acc in
          bind_app a' ~pattern ~acc)
      | _, _ ->
        None

  let rec do_for_match :
  type r s . ('i, r) E.t ->
    pattern  :  ('i, s) t ->
    f        :  ('i binding list -> unit) ->
    unit =
    fun m ~pattern ~f ->
      match pattern, m with
      | M_Var id, _ ->
        (match Id.type_of_t id, E.type_of_t m with
        | Type.Y_Int, Type.Y_Int ->
          f [`Int (id, m)]
        | Type.Y_Bool, Type.Y_Bool ->
          f [`Bool (id, m)]
        | _, _ ->
          raise (Unreachable.Exn _here_))
      | M_App (_, _), (E.M_App (a, b) as m) ->
        bind_app m ~pattern |> Option.iter ~f
      | _, _ ->
        ()

end

module Box = struct
  type 'i t = Box : ('i, 'r) M.t -> 'i t
end

module Box_arrow = struct
  type 'i t = Box : ('i, 'r -> 's) M.t -> 'i t
end
