(* wildcard pats in multi-arity functions

-- args: --vv --phase elab
-- expected stdout:
-- val m: int -> int -> int = fn x0 => fn x1 => 
--   let
--     val x3: int -> int = fn x => x
--     val x4: int -> int = fn y => y
--     val x6: unit -> int = fn x5 => 0
--   in 
--     
--       case x0
--         of 0 => 
--           case x1
--             of 0 => x3 x0
--              | _ => x4 x1
--          | _ => 
--              case x1
--                of 0 => x3 x0
--                 | _ => x6 ()
--   end

*)

fun m x 0 = x
  | m 0 y = y
  | m _   = 0