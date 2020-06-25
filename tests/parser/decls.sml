datatype 'a option = None | Some of 'a

datatype expr = Unit | Var of int | App of expr * expr | Abs of ty * expr
     and ty = TyUnit | TyArrow of ty * ty 


(* We use a modified grammar, where case statements have an explicit end *)
fun ('a, 'b) >>= (x: 'a option) (f: 'a -> 'b option) : 'b option 
    =   case x of 
            | Some a => f a 
            | None   => None
        end

val return  : ('a -> 'a option) = fn x => Some x
val >>= : ('a option -> ('a -> 'b option) -> 'b option) 
    = fn (Some a) f => f a
        | None    f => None 

fun $ f g = f g

infix 6 >>=
infixr 10 $

val x = Some 10;
val y = x >>= fn (x : int) => return $ x + 1;

val x = let
    val x = 10;
    val y = let
      val q = 10;
      fun map nil     f = nil
        | map (x::xs) f = (f x :: map xs f);
        
    in
      body
    end
in
  {label = x, value = (Some x) >>= fn x => x + 1 }
end

datatype bool = true | false 

val x = case true 
          of true   => 1
           | y  => y
        end


