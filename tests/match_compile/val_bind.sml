(* give warning on top-level non-exhaustive value binding

-- args: --vv --phase elab
-- expected stdout:
-- 1 warnings, 0 errors
-- val (x, y): int * int list = 
--   let
--     val x2: int * int list -> int * int list = fn x1 => 
--       let
--         val (x, y): int * int list = x1
--       in 
--         (x, y)
--       end
--     val x0: int list = [1, 2, 3]
--   in 
--     
--       case x0
--         of :: x3 => 
--           let
--             val (x4, x5): int * int list = x3
--           in 
--             x2 (x4, x5)
--           end
--          | _ => raise Bind
--   end

-- expected stderr:
-- Warn
-- 34 | 
-- 35 | val x::y = [1,2,3]
--           ^~~~~~~~~~~~~^ inexhaustive `val` binding

*)

val x::y = [1,2,3]