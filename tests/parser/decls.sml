datatype 'a option = None | Some of 'a

val + = primitive "Int.add" : int * int -> int
infix 3 +
val _ = 1 :: 2 :: nil

datatype expr = Unit | Var of int | App of expr * expr | Abs of ty * expr
     and ty = TyUnit | TyArrow of ty * ty 

fun >>= ((Some x), f) = f x 
  | >>= (None  , f) = None

val return = Some
infix 6 >>=

val x = Some 10;
val y = x >>= (fn x => Some (x + 1))

fun f m = let val y = m; val x = y true in x end