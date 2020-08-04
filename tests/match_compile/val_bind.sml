(* give warning on top-level non-exhaustive value binding

-- args: --vv
-- expected stdout:
-- val (x, y): int * int list = 
--   let
--     val c: int * int list -> int * int list = fn b => 
--       let
--         val (x, y): int * int list = b
--       in 
--         (x, y)
--       end
--     val a: int list = [1, 2, 3]
--   in 
--     
--       case a
--         of :: d => 
--           let
--             val (e, f): int * int list = d
--           in 
--             c (e, f)
--           end
--          | _ => raise Bind
--   end
-- 1 warnings, 0 errors

-- expected stderr:
-- Warn
-- 34 | 
-- 35 | val x::y = [1,2,3]
--           ^~~~~~~~~~~~~^ inexhaustive `val` binding

*)

val x::y = [1,2,3]