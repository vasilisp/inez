open Camlp4.PreCast

let gensym =
  let cnt = ref 0 in
  fun ?(prefix = "_x") () ->
    incr cnt;
    Printf.sprintf "%s__%03i_" prefix !cnt

let uf_ast_fun _loc mid mid' (l, rtype) =
  let fold l init =
    let f y acc =
      match y with
      | `Int ->
        <:expr< Type.Y_Int_Arrow $acc$ >>
      | `Bool ->
        <:expr< Type.Y_Bool_Arrow $acc$ >> in
    ListLabels.fold_right l ~f ~init
  and init =
    match rtype with
    | `Int -> <:expr< Type.Y_Int >>
    | `Bool -> <:expr< Type.Y_Bool >>
  and ret e =
    <:expr< $uid:mid$.M.M_Var (Id_for_scripts.gen_id $e$) >> in
  ret (fold l init)

let uf_ast_apps _loc mid init =
  ListLabels.fold_left2 ~init
    ~f:(fun acc id t ->
      let t =
        match t with
        | `Int ->
          <:expr< $id:id$ >>
        | `Bool ->
          <:expr< $uid:mid$.M.M_Bool $id:id$ >> in
      <:expr< $uid:mid$.M.M_App ($acc$, $t$) >>)

let ml_lambda_abstract _loc init =
  let f id acc = <:expr< fun $id:id$ -> $acc$ >> in
  ListLabels.fold_right ~init ~f

let uf_maybe_convert _loc mid y e =
  match y with
  | `Bool ->
    <:expr< Formula.F_Atom ($uid:mid$.A.A_Bool ($e$)) >>
  | `Int ->
    e

let uf_ast _loc mid mid' (l, y) =
  let l_ids =
    let f _ = Ast.IdLid (_loc, gensym ()) in
    ListLabels.map l ~f
  and id = gensym ~prefix:"__uf_" () in
  let inside =
    ml_lambda_abstract _loc
      (uf_maybe_convert _loc mid y
         (uf_ast_apps _loc mid <:expr< $lid:id$ >> l_ids l))
      l_ids
  and binding = uf_ast_fun _loc  mid mid' (l, y) in
  <:expr< let $lid:id$ = $binding$ in $inside$ >> ;;

let rec type_of_uf ?acc:(acc = []) =
  function
  | <:expr< fun $lid:_$ -> $e$ >>
  | <:expr< fun _ -> $e$ >>
  | <:expr< fun ($lid:_$ : Int) -> $e$ >>
  | <:expr< fun (_ : Int) -> $e$ >> ->
    type_of_uf ~acc:(`Int :: acc) e
  | <:expr< fun ($lid:_$ : Bool) -> $e$ >>
  | <:expr< fun (_ : Bool) -> $e$ >> ->
    type_of_uf ~acc:(`Bool :: acc) e
  | <:expr< ~free >>
  | <:expr< (~free : Int) >> ->
    Some (ListLabels.rev acc, `Int)
  | <:expr< (~free : Bool) >> ->
    Some (ListLabels.rev acc, `Bool)
  | _ ->
    None

let map_uf mid mid' = object

  inherit Ast.map as super
  
  method expr = function
  | <:expr@loc< fun $lid:_$ -> $_$ >>
  | <:expr@loc< fun ($lid:_$ : Int) -> $_$ >>
  | <:expr@loc< fun ($lid:_$ : Bool) -> $_$ >>
  | <:expr@loc< fun _ -> $_$ >>
  | <:expr@loc< fun (_ : Int) -> $_$ >>
  | <:expr@loc< fun (_ : Bool) -> $_$ >> as e ->
    (match type_of_uf e with
    | Some y ->
      uf_ast loc mid mid' y
    | None ->
      super#expr e)
  | e ->
    super#expr e

end

let transform_logic_aux mid e =
  let _loc = Ast.loc_of_expr e in
  match e with
  | <:expr< true >> ->
    <:expr< Formula.F_True >>
  | <:expr< false >> ->
    <:expr< Formula.(F_Not F_True) >>
  | <:expr< $uid:mid$.M.M_Int $x$ * $uid:mid'$.M.M_Int $y$ >>
      when mid = mid' ->
    <:expr< $uid:mid$.M.M_Int (Int63.( * ) $x$ $y$) >>
  | <:expr<
      $uid:mid$.M.M_Int (Core.Std.Int63.of_string $str:s$) * $x$ >> ->
    <:expr<
      $uid:mid$.M.M_Prod (Core.Std.Int63.of_string $str:s$, $x$) >>
  | <:expr< $uid:mid$.M.M_Int $i1$ * $uid:mid'$.M.M_Int $i2$ >>
      when mid = mid' ->
    <:expr< $uid:mid$.M.M_Int (Core.Std.Int63.(i1 * i2)) >>
  | <:expr< $int:s$ >> ->
    <:expr< $uid:mid$.M.M_Int (Core.Std.Int63.of_string $str:s$) >>
  | <:expr< $int64:s$ >> ->
    <:expr< $uid:mid$.M.M_Int (Core.Std.Int63.of_string $str:s$) >>
  | _ ->
    e

let map_logic_aux mid =
  Ast.map_expr (transform_logic_aux mid)

let transform_logic mid = function
  | <:expr@loc< ~logic $e$ >> ->
    <:expr@loc< let open $uid:mid$.Ops in
                $(map_logic_aux mid)#expr e$ >>
  | e ->
    e

let map_logic mid =
  Ast.map_expr (transform_logic mid)

let rec extract_quantifiers e ~acc =
  match e with
  | <:expr@loc< ~forall $lid:v$ $g$ >> ->
    let acc = v :: acc in
    extract_quantifiers g ~acc
  | e ->
    ListLabels.rev acc, e

let bind_quantified _loc l init =
  let l =
    let f i = <:binding<
      $lid:i$ = Id_for_scripts.gen_id Type.Y_Int >> in
    ListLabels.map l ~f in
  <:expr< let $list:l$ in $init$ >>

let bind_quantified_as_exprs _loc mid l init =
  let l =
    let f i = <:binding< $lid:i$ = $uid:mid$.M.M_Var $lid:i$ >> in
    ListLabels.map l ~f in
  <:expr< let $list:l$ in $init$ >>

let rec list_of_quantified _loc l =
  let init = <:expr< [] >>
  and f i acc = <:expr< $lid:i$ :: $acc$ >> in
  ListLabels.fold_right l ~f ~init
  
let map_forall mid mid' = object

  inherit Ast.map as super
  
  method expr = function
  | <:expr@loc< ~forall $lid:v$ $e$ >> ->
    let l, e =
      let acc = [v] in
      extract_quantifiers e ~acc in
    let e = (map_logic_aux mid)#expr e in
    let e = <:expr@loc< let open $uid:mid'$.Ops in $e$ >> in
    (<:expr@loc<
        ($list_of_quantified loc l$,
         $bind_quantified_as_exprs loc mid l e$) >>) |>
        bind_quantified loc l
  | e ->
    super#expr e

end
