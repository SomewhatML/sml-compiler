(* check recursion

-- args: --v --phase elab
-- expected stdout:
-- val recurse: nat -> nat -> nat -> nat
-- val o: 'a -> 'b * 'c -> 'a -> 'c -> 'b
-- val four: nat

*)

datatype nat = Z | S of nat 

fun recurse f Z = f Z
  | recurse f (S n) = f (recurse f n)


fun o (f, g) = fn x => f (g x)
infixr 3 o

val four = recurse (S o S) (S  Z);