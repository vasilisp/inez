type 'a formula

val true': 'a formula
val false': 'a formula

val not: 'a formula -> 'a formula
val (&&): 'a formula -> 'a formula -> 'a formula
val (||): 'a formula -> 'a formula -> 'a formula
val (=>): 'a formula -> 'a formula -> 'a formula
val ite: 'a formula -> 'a formula -> 'a formula -> 'a formula
 
