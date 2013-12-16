open Core.Std
open Logic

module Make (Imt : Imt_intf.S_with_cut_gen) (I : Id.S) = struct

  type occ = Imt.ivar list

  type instantiator = occ -> Imt.ivar Terminology.iexpr

  type axiom = occ list ref * instantiator

  module Theory_solver = struct

    type ctx = {
      mutable r_next_id : int;
      r_axioms_h        : axiom Int.Table.t
    }

    let make_ctx () = {
      r_next_id  = 0;
      r_axioms_h = Int.Table.create ~size:128 ()
    }

    module F

      (S : Imt_intf.S_dp_access_bounds
       with type ivar = Imt.ivar
       and type bvar = Imt.bvar) =

    struct

      let check r r' _ = true

      let backtrack r r' = ()

      let push_level r r' = ()

      let generate_axiom r r' (occs, f) =
        (* FIXME: decide on bounds convention *)
        let f v =
          match S.get_lb_local r' v with
          | Some v ->
            Int63.(v >= zero)
          | None ->
            false in
        let f = List.for_all ~f in
        let lt, lf = List.partition_tf !occs ~f in
        match lt with
        | _ :: _ ->
          List.iter lt ~f:(Fn.compose (S.add_cut_local r') f);
          occs := lf;
          true
        | _ ->
          false

      let generate ({r_axioms_h} as r) r' =
        if
          let f ~key ~data acc = generate_axiom r r' data || acc
          and init = false in
          Hashtbl.fold r_axioms_h ~init ~f
        then
          `Ok
        else
          `Fail

    end

    let assert_axiom ({r_next_id = id; r_axioms_h} as r) f =
      r.r_next_id <- id + 1;
      Hashtbl.replace r_axioms_h id (ref [], f)

    let assert_instance {r_axioms_h} id l =
      let ({contents} as occs), _ = Hashtbl.find_exn r_axioms_h id in
      occs.contents <- l @ contents

  end

  include Imt.F(Theory_solver)

end 
