(* wildcard pats in multi-arity functions

-- args: --vv --phase elab
-- expected stdout:
-- val m: int -> int -> int = fn x0 => fn x1 => 
--   let
--     val x4: int -> int = fn x3 => x3
--     val x6: int -> int = fn x5 => x5
--     val x8: unit -> int = fn x7 => 0
--   in 
--     
--       case x0
--         of 0 => 
--           case x1
--             of 0 => x4 x0
--              | _ => x6 x1
--          | _ => 
--              case x1
--                of 0 => x4 x0
--                 | _ => x8 ()
--   end

*)

fun m x 0 = x
  | m 0 y = y
  | m _   = 0