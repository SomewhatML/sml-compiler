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

val x = let
    val x = 10;
    val y = let
      val q = 10;
      fun map nil     f = nil
        | map (x::xs) f = (f x :: map xs f);
        
    in
      y
    end
in
  {label = x, value = (Some x) >>= (fn x => Some(x + 1)) }
end
