open Core.Std

type ibtype = E_Int | E_Bool
with sexp

module U = struct

  (* non-GADT version of t (defined later)  *)

  type t =
  | Y_Int
  | Y_Bool
  | Y_Int_Arrow   of t
  | Y_Bool_Arrow  of t

  with compare, sexp

end

module T = struct

  type _ t =
  | Y_Int         :  int t
  | Y_Bool        :  bool t
  | Y_Int_Arrow   :  'a t -> (int -> 'a) t
  | Y_Bool_Arrow  :  'a t -> (bool -> 'a) t

  let rec ungadt_t :
  type s . s t -> U.t =
    function
    | Y_Int ->
      U.Y_Int
    | Y_Bool ->
      U.Y_Bool
    | Y_Int_Arrow y ->
      U.Y_Int_Arrow (ungadt_t y)
    | Y_Bool_Arrow y ->
      U.Y_Bool_Arrow (ungadt_t y)

  let compare x y =
    U.compare (ungadt_t x) (ungadt_t y)

  let sexp_of_t f a =
    U.sexp_of_t (ungadt_t a)

  let int_t_of_sexp x =
    match (U.t_of_sexp x) with
    | U.Y_Int ->
      Y_Int
    | _ ->
      raise (Sexp.Of_sexp_error
               (Util.Exn ("int_t_of_sexp", _here_), x))

  let bool_t_of_sexp x =
    match (U.t_of_sexp x) with
    | U.Y_Bool ->
      Y_Bool
    | _ ->
      raise (Sexp.Of_sexp_error
               (Util.Exn ("bool_t_of_sexp", _here_), x))

  let count_arrows t =
    let rec ca_aux : type s . int -> s t -> int = fun acc -> function
      | Y_Int ->
        acc
      | Y_Bool ->
        acc
      | Y_Int_Arrow y ->
        ca_aux (1 + acc) y
      | Y_Bool_Arrow y ->
        ca_aux (1 + acc) y in
    ca_aux 0 t

  let t_of_app :
  type r s . (r -> s) t -> r t -> s t =
    fun x y -> match x, y with
    | Y_Int_Arrow x, Y_Int ->
      x
    | Y_Bool_Arrow x, Y_Bool ->
      x

  let rec rightmost_ibtype_of_t :
  type s . s t -> ibtype =
    function
    | Y_Int -> E_Int
    | Y_Bool -> E_Bool
    | Y_Int_Arrow y -> rightmost_ibtype_of_t y
    | Y_Bool_Arrow y -> rightmost_ibtype_of_t y

end

include T

module Box = struct

  type t = Box : _ T.t -> t

  let t_of_ibtype = function
    | E_Int ->
      Box Y_Int
    | E_Bool ->
      Box Y_Bool

  let compare (Box x) (Box y) =
    U.compare (ungadt_t x) (ungadt_t y)

  let sexp_of_t (Box x) =
    let f _ = Sexplib.Sexp.Atom "" in
    let x = sexp_of_t f x in
    Sexplib.Sexp.(List [Atom "Box"; x])

end
