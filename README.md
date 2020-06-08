# SimpleML

SimpleML is a toy Standard ML compiler


```
fun main (x : 'a) (y : ∀'b. 'b -> 'b) : 'a 
    = y x

fun main : 'a -> forall 'b. 'b -> 'b) -> 'a
    | x f = f x

fun 'a main x y : int = x + y
     | main 9 0 : int = 10
and do_it nil = 0
  | do_it (x::xs) = 1 + do_it xs


```