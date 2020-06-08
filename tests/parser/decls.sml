datatype 'a option = None | Some of 'a

datatype expr = Unit | Var of int | App of expr * expr | Abs of ty * expr
     and ty = TyUnit | TyArrow of ty * ty 


fun ('a, 'b) >>= (x: 'a option) (f: 'a -> 'b option) : 'b option 
    = case x of 
        | Some a => f a 
        | None   => None
    end

val >>= : ('a option -> ('a -> 'b option) -> 'b option) 
    = fn (Some a) f => f a
        | None    f => None 

infix 6 >>=
