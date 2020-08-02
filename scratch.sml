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

(* STLC type checking *)
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
  | merge (x::xs) (y::ys) = x::y::(merge xs ys);

(* example from Compiling Pattern Matching *)
let 
  datatype u = T | F
  val x = (T, F, T) 
in 
  case (T, F, T) of
      | (_, F, T) => 1
      | (F, T, _) => 2
      | (_, _, F) => 3
      | (_, _, T) => 4
    end
end

(* example from MLton's MatchCompile docs *)
datatype 'a c = C1 of 'a | C2 of 'a | C3 of 'a 
val e1 = 1
val e2 = 2
val x = (C1 10, C1 9)
val _ = case x of
  | (_, C1 a) => e1
  | (C2 b, C3 c) => e2
end
