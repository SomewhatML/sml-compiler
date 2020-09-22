(* test pattern match compilation to decision trees

-- args: --vv --phase elab
-- expected stdout:
-- val 'a merge: 'a list -> 'a list -> 'a list = fn x3 => fn x4 => 
--   let
--     val x0: 'a list -> 'a list = fn xs => xs
--     val x1: 'a list -> 'a list = fn ys => ys
--     val x2: 'a * 'a list * 'a * 'a list -> 'a list = fn x6 => 
--       let
--         val x: 'a = #1 x6
--         val xs: 'a list = #2 x6
--         val y: 'a = #3 x6
--         val ys: 'a list = #4 x6
--       in 
--         :: (x, :: (y, merge xs ys))
--       end
--   in 
--     
--       case x3
--         of nil => 
--           case x4
--             of nil => x0 x3
--              | _ => x1 x4
--          | :: x9 => 
--              let
--                val x10: 'a = #1 x9
--                val x11: 'a list = #2 x9
--              in 
--                
--                  case x4
--                    of nil => x0 x3
--                     | :: x13 => 
--                         let
--                           val x14: 'a = #1 x13
--                           val x15: 'a list = #2 x13
--                         in 
--                           x2 (x10, x11, x14, x15)
--                         end
--              end
--   end

*)

fun merge xs [] = xs 
  | merge [] ys = ys 
  | merge (x::xs) (y::ys) = x::y::merge xs ys