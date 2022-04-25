datatype 'a T = Left of 'a | Right of int

(* fun map f [] = []
  | map f (x::xs) = f x :: map f xs *)

val y = Left 10
val xz = [y, Right 78]
(* val z = [Right 12, Left "hello"] *)
val z =
  Right 12 :: Left "hello" :: nil
   

  (* val xs = map Left ["a", "b"] *)(* val ys = map Right [1, 2, 3] *)
