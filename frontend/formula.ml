type 't formula =
  F_True
| F_Ground  of  't
| F_Not     of  't formula
| F_And     of  't formula list

let not g = F_Not g

let (&&) g h = F_And [g; h]

let (||) g h = not (not g && not h)

let (=>) g h = not g || h

let true' = F_True
let false' = F_Not F_True
