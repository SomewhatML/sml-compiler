(* Check that type unification will fail in obvious cases

-- args: --v
-- expected stdout:
-- val +: int * int -> int
-- val add: int -> int -> int
-- val _: int
-- 
-- 0 warnings, 1 errors

-- expected stderr:
-- Error
-- 22,9 Type unification: can't unify function with argument types. Type constructors differ: int, bool

*)

val + = primitive "Int.add" : int * int -> int 
infix 3 +

fun add x y = x + y

val _ = add 3 true