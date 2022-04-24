(* check elaboration of exceptions 

-- args: --v --phase elab
-- expected stdout:
-- val try: int -> int
-- val x: int

*)

exception EX of int
(* exception EX2 of int *)

fun try 0 = raise (EX 0)
  | try n = n

val x = try 1 handle (EX x) => 1