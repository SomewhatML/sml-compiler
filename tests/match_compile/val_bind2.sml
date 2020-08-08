(* check that elaboration of variable patterns does not become complicated

-- args: --vv --phase elab
-- expected stdout:
-- val x: int = 
--   let
--     val x1: int -> int = fn x => x
--     val x0: int = 1
--   in 
--     x1 x0
--   end

*)

val x = 1