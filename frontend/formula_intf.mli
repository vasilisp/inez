module type S = sig

  type 't formula

  val not: 't formula -> 't formula
  val (&&): 't formula -> 't formula -> 't formula
  val (||): 't formula -> 't formula -> 't formula
  val (=>): 't formula -> 't formula -> 't formula

  val true': 't formula
  val false': 't formula

end
