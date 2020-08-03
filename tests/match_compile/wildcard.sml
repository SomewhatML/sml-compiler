(* wildcard pats in multi-arity functions

-- args: --vv
-- expected stdout:
-- val m: int -> int -> int = fn a => fn b => 
--   let
--     val e: int -> int = fn d => 
--       let
--         val x: int = d
--       in 
--         x
--       end
--     val g: int -> int = fn f => 
--       let
--         val y: int = f
--       in 
--         y
--       end
--     val i: unit -> int = fn h => 0
--   in 
--     
--       case a
--         of 0 => 
--           case b
--             of 0 => e a
--              | _ => g b
--          | _ => 
--              case b
--                of 0 => e a
--                 | _ => i ()
--   end
-- 

*)

fun m x 0 = x
  | m 0 y = y
  | m _   = 0