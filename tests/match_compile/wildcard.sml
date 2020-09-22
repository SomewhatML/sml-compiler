(* wildcard pats in multi-arity functions

-- args: --vv --phase elab
-- expected stdout:
-- val m = fn x3 => fn x4 => 
--   let
--     val x0 = fn x => x
--     val x1 = fn y => y
--     val x2 = fn x6 => 0
--   in 
--     
--       case x3
--         of 0 => 
--           case x4
--             of 0 => x0 x3
--              | _ => x1 x4
--          | _ => 
--              case x4
--                of 0 => x0 x3
--                 | _ => x2 ()
--   end

*)

fun m x 0 = x
  | m 0 y = y
  | m _   = 0