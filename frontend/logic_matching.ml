open Core.Std

module Make (M : Logic_intf.Term_with_ops) = struct

  type 'i box = Box : ('i, _) M.t -> 'i box

  let rec fun_id_of_app :
  type r s . ('i, r) M.t ->  'i Id.Box.t option =
    function
    | M.M_App (M.M_Var id, _) ->
      Some (Id.Box.Box id)
    | M.M_App (f, _) ->
      fun_id_of_app f
    | _ ->
      None

  let rec args_of_app :
  type s . ('i, s) M.t -> acc:'i box list -> 'i box list option =
    fun m ~acc ->
      match m with
      | M.M_App (M.M_Var id, a) ->
        Some (Box a :: acc)
      | M.M_App (f, a) ->
        let acc = Box a :: acc in
        args_of_app f ~acc
      | _ ->
        None

  let rec terms_of_sum m ~coef ~acc =
    match m with
    | M.M_Sum (m1, m2) ->
      let acc = terms_of_sum m1 ~coef ~acc in
      terms_of_sum m2 ~coef ~acc
    | M.M_Prod (c, m) ->
      let coef = Int63.(c * coef) in
      terms_of_sum m ~coef ~acc
    | _ ->
      (coef, m) :: acc

  type ('i, 'c) bindings = (('i, int) Id.t, ('i, int) M.t, 'c) Map.t

  let try_bind id m ~ids ~bindings =
    if Set.mem ids id then    
      match Map.find bindings id with
      | Some _ ->
        None
      | None ->
        Some (Map.add bindings id m)
    else
      None

  let try_bind :
  type r s . ('i, r) Id.t ->
    ('i, s) M.t ->
    ids       :  (('i, int) Id.t, 'c) Set.t ->
    bindings  :  ('i, 'c) bindings ->
    ('i, 'c) bindings option =
    fun id m ~ids ~bindings ->
      match Id.type_of_t id, M.type_of_t m with
      | Type.Y_Int, Type.Y_Int ->
        try_bind id m ~ids ~bindings
      | _ ->
        None

  let rec arg_list_matches l ~patterns  ~ids ~bindings =
    match patterns, l with
    | Some patterns, Some l when List.(length patterns = length l) ->
      let f acc (Box pattern) (Box m) =
        let f bindings = matches m ~pattern ~ids ~bindings in
        Option.(acc >>= f) in
      List.fold2_exn l patterns ~f ~init:(Some bindings)
    | _ ->
      None

  and matches :
  type r s . ('i, r) M.t ->
    pattern  : ('i, s) M.t ->
    ids      : (('i, int) Id.t, 'c) Set.t ->
    bindings : ('i, 'c) bindings ->
    ('i, 'c) bindings option =
    fun m ~pattern ~ids ~bindings ->
      match pattern, m with
      | M.M_Sum _, _ ->
        None
      | M.M_Ite (_, _, _), _ ->
        None
      | M.M_Int _, _ ->
        None
      | M.M_Var v, _ ->
        try_bind v m ~ids ~bindings
      | M.M_Prod (c1, pattern), M.M_Prod (c2, m) when c1 = c2 ->
        matches m ~pattern ~ids ~bindings
      | M.M_App _, M.M_App _ when
          compare (fun_id_of_app pattern) (fun_id_of_app m) = 0 ->
        let patterns = args_of_app pattern ~acc:[]
        and args = args_of_app m ~acc:[] in
        arg_list_matches args ~patterns ~ids ~bindings
      | _ ->
        None

  let matches_subterm :
  type r s . ('i, r) M.t ->
    pattern  : ('i, s) M.t ->
    ids      : (('i, int) Id.t, 'c) Set.t ->
    ff       : ('i M.atom Formula.t -> ('i, 'c) bindings option) ->
    ('i, 'c) bindings option =
    fun m ~pattern ~ids ~ff ->
      let bindings = Map.Poly.empty in
      let f = matches ~pattern ~ids ~bindings in
      let f_pair a b =
        let default () = f b in
        Util.try_again (f a) ~default in
      match f m with
      | Some _ as b ->
        b
      | None ->
        (match m with
        | M.M_Bool b ->
          ff b
        | M.M_Sum (m1, m2) ->
          f_pair m1 m2
        | M.M_Prod (_, m) ->
          f m
        | M.M_Ite (c, a, b) ->
          (match ff c with
          | Some _ as b ->
            b
          | None ->
            f_pair a b)
        | M.M_App (a, b) ->
          f_pair a b
        | M.M_Int _ ->
          None
        | M.M_Var _ ->
          None)

end
