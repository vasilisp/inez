open Core.Std

module LL = struct
  let (<=) lb lb' =
    let lb =  Option.value lb  ~default:Int63.min_value
    and lb' = Option.value lb' ~default:Int63.min_value in
    Int63.(lb <= lb')
end

module UU = struct
  let (<=) ub ub' =
    let ub  = Option.value ub  ~default:Int63.max_value
    and ub' = Option.value ub' ~default:Int63.max_value in
    Int63.(ub <= ub')
end
  
module LU = struct
  let (<=) lb ub =
    let lb = Option.value lb ~default:Int63.min_value
    and ub = Option.value ub ~default:Int63.max_value in
    Int63.(lb <= ub)
end

module UL = struct
  let (<=) a b = LU.(b <= a)
end
