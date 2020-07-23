datatype 'a option = None | Some of 'a

val + = primitive "Int.add" : int * int -> int
infix 3 +

val 'a == = primitive "Eq.poly" : 'a * 'a -> bool
infix 3 == 
val - = primitive "Int.sub" : int * int -> int
infix 3 -
val _ = 1 :: 2 :: nil

datatype expr = Unit | Var of int | App of expr * expr | Abs of ty * expr
     and ty = TyUnit | TyArrow of ty * ty 

fun >>= ((Some x), f) = f x 
  | >>= (None  , f) = None

fun length (x::xs)  = 1 + length xs 
  | length []       = 0

val return = Some
infix 6 >>=

val x = Some 10;
val y = x >>= (fn x => Some (x + 1))

fun f m = let val y = m; val x = y true in x end

fun index _ []      = None 
  | index 0 (x::_)  = Some x 
  | index x (_::xs) = index (x - 1) xs

exception CantType
exception Unwrap
fun unwrap (Some x) = x 
  | unwrap None     = raise Unwrap 

fun type_check ctx Unit         = TyUnit
  | type_check ctx (Var x)      = unwrap (index x ctx)
  | type_check ctx (App (e1, e2))  = let 
      val t1 = type_check ctx e1 
      val t2 = type_check ctx e2 
    in 
      case t1
        of TyArrow(t11, t12) => if t2 == t11 then t12 else raise CantType
         | _                 => raise CantType
      end 
    end 
  | type_check ctx (Abs (ty, e)) = TyArrow (ty, type_check (ty::ctx) e)

fun merge xs [] = xs 
  | merge [] ys = ys 
  | merge (x::xs) (y::ys) = x::ys
