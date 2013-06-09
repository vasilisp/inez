open Camlp4.PreCast

exception Reserved of string

let gensym =
  let cnt = ref 0 in
  fun ?(prefix = "_x") () ->
    incr cnt;
    Printf.sprintf "%s__%03i_" prefix !cnt

let uf_ast_fun _loc mid (l, rtype) =
  let fold l init =
    let f y acc =
      match y with
      | Type.E_Int ->
        <:expr< Type.Y_Int_Arrow $acc$ >>
      | Type.E_Bool ->
        <:expr< Type.Y_Bool_Arrow $acc$ >> in
    ListLabels.fold_right l ~f ~init
  and ret e = <:expr< $uid:mid$.M.M_Var (gen_id $e$) >> in
  match rtype with
  | Type.E_Int ->
    ret (fold l <:expr< Type.Y_Int >>)
  | Type.E_Bool ->
    ret (fold l <:expr< Type.Y_Bool >>)

let uf_ast_apps _loc mid init =
  ListLabels.fold_right2 ~init
    ~f:(fun id t acc ->
      let t =
        match t with
        | Type.E_Int ->
          <:expr< $id:id$ >>
        | Type.E_Bool ->
          <:expr< $uid:mid$.M.M_Bool $id:id$ >> in
      <:expr< $uid:mid$.M.M_App ($acc$, $t$) >>)

let uf_ast_mlfun _loc init =
  let f id acc = <:expr< fun $id:id$ -> $acc$ >> in
  ListLabels.fold_right ~init ~f

let uf_maybe_convert _loc mid y e =
  match y with
  | Type.E_Bool ->
    <:expr< Formula.F_Atom ($uid:mid$.A.A_Bool ($e$)) >>
  | Type.E_Int ->
    e

let uf_ast _loc mid (l, y) =
  let l_ids =
    let f _ = Ast.IdLid (_loc, gensym ()) in
    List.map f l
  and id = gensym ~prefix:"__uf_" () in
  let inside =
    uf_ast_mlfun _loc
      (uf_maybe_convert _loc mid y
         (uf_ast_apps _loc mid <:expr< $lid:id$ >> l_ids l))
      l_ids
  and binding = uf_ast_fun _loc mid (l, y) in
  <:expr< let $lid:id$ = $binding$ in $inside$ >> ;;

let rec type_of_uf ?acc:(acc = []) =
  function
  | <:expr< fun ($lid:_$ : Int) -> $e$ >>
  | <:expr< fun (_ : Int) -> $e$ >> ->
    type_of_uf ~acc:(Type.E_Int :: acc) e
  | <:expr< fun ($lid:_$ : Bool) -> $e$ >>
  | <:expr< fun (_ : Bool) -> $e$ >> ->
    type_of_uf ~acc:(Type.E_Bool :: acc) e
  | <:expr< (free : Int) >>
  | <:expr< free >> ->
    Some (List.rev acc, Type.E_Int)
  | <:expr< (free : Bool) >> ->
    Some (List.rev acc, Type.E_Bool)
  | _ ->
    None

let map_uf mid = object
    
  inherit Ast.map as super

  method expr e =
    match e with
    | <:expr@loc< fun ($lid:_$ : Int) -> $_$ >>
    | <:expr@loc< fun ($lid:_$ : Bool) -> $_$ >>
    | <:expr@loc< fun (_ : Int) -> $_$ >>
    | <:expr@loc< fun (_ : Bool) -> $_$ >> ->
      (match type_of_uf e with
      | Some y ->
        uf_ast loc mid y
      | None ->
        e)
    | <:expr@loc< free >> ->
      Loc.raise loc (Reserved "free")
    | _ ->
      super#expr e

  method ident = function
  | <:ident@loc< free >> ->
    Loc.raise loc (Reserved "free")
  | i ->
    super#ident i

end

let transform_logic_aux mid e =
  let _loc = Ast.loc_of_expr e in
  match e with
  | <:expr< true >> ->
    <:expr< Formula.F_True >>
  | <:expr< false >> ->
    <:expr< Formula.(F_Not F_True) >>
  | <:expr< $int:s$ >> ->
    <:expr< $uid:mid$.M.M_Int (Core.Std.Int63.of_string $str:s$) >>
  | <:expr< $int64:s$ >> ->
    <:expr< $uid:mid$.M.M_Int (Core.Std.Int63.of_string $str:s$) >>
  | _ ->
    e

let map_logic_aux mid =
  Ast.map_expr (transform_logic_aux mid)

let transform_logic mid e =
  match e with
  | <:expr@loc< let _ = ~logic in $e'$ >>
  | <:expr@loc< let () = ~logic in $e'$ >> ->
    <:expr@loc< let open $uid:mid$.Ops in
                $(map_logic_aux mid)#expr e'$ >>
  | e ->
    e

let map_logic mid =
  Ast.map_expr (transform_logic mid)
