datatype 'a T = Left of 'a | Right of int

(* fun map f [] = []
  | map f (x::xs) = f x :: map f xs *)

val y = Left 10
val z = Right 12
val a = Left "hello"
(* val xs = map Left ["a", "b"] *)
(* val ys = map Right [1, 2, 3] *)
