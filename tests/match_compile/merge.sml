(* test pattern match compilation to decision trees

-- args: --vv --phase elab
-- expected stdout:
-- val 'a merge: 'a list -> 'a list -> 'a list = fn x0 => fn x1 => 
--   let
--     val x4: 'a list -> 'a list = fn x3 => x3
--     val x6: 'a list -> 'a list = fn x5 => x5
--     val x8: 'a * 'a list * 'a * 'a list -> 'a list = fn x7 => 
--       let
--         val (x, xs, y, ys): 'a * 'a list * 'a * 'a list = x7
--       in 
--         :: (x, :: (y, merge xs ys))
--       end
--   in 
--     
--       case x0
--         of nil => 
--           case x1
--             of nil => x4 x0
--              | _ => x6 x1
--          | :: x11 => 
--              let
--                val (x12, x13): 'a * 'a list = x11
--              in 
--                
--                  case x1
--                    of nil => x4 x0
--                     | :: x15 => 
--                         let
--                           val (x16, x17): 'a * 'a list = x15
--                         in 
--                           x8 (x12, x13, x16, x17)
--                         end
--              end
--   end

*)

fun merge xs [] = xs 
  | merge [] ys = ys 
  | merge (x::xs) (y::ys) = x::y::merge xs ys