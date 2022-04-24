fun doit x = (x, x)

val foo = doit 10
val bar = doit {a=10, b="hello"}

val quux = let
    val inner = fn x => x
in (inner 10, inner "foo") end

datatype 'a Sum = Left of 'a | Right of int

val x = fn Left x => x
         | Right y => y