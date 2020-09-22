(* give warning on top-level non-exhaustive value binding

-- args: --vv --phase elab
-- expected stdout:
-- 1 warnings, 0 errors
-- val x2: int * int list = 
--   let
--     val x0 = fn x3 => 
--       let
--         val x: int = #1 x3
--         val y: int list = #2 x3
--       in 
--         (x, y)
--       end
--     val x1: int list = [1, 2, 3]
--   in 
--     
--       case x1
--         of :: x4 => 
--           let
--             val x5: int = #1 x4
--             val x6: int list = #2 x4
--           in 
--             x0 (x5, x6)
--           end
--          | _ => raise Bind
--   end
-- val x: int = #1 x2
-- val y: int list = #2 x2

-- expected stderr:
-- Warn
-- 38 | 
-- 39 | val x::y = [1,2,3]
--           ^~~~~~~~~~~~~^ inexhaustive `val` binding

*)

val x::y = [1,2,3]