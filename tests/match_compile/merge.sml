(* test pattern match compilation to decision trees

-- args: --vv --phase elab
-- expected stdout:
-- val 'a merge: 'a list -> 'a list -> 'a list = fn x0 => fn x1 => 
--   let
--     val x3: 'a list -> 'a list = fn xs => xs
--     val x4: 'a list -> 'a list = fn ys => ys
--     val x6: 'a * 'a list * 'a * 'a list -> 'a list = fn x5 => 
--       let
--         val (x, xs, y, ys): 'a * 'a list * 'a * 'a list = x5
--       in 
--         :: (x, :: (y, merge xs ys))
--       end
--   in 
--     
--       case x0
--         of nil => 
--           case x1
--             of nil => x3 x0
--              | _ => x4 x1
--          | :: x9 => 
--              let
--                val (x10, x11): 'a * 'a list = x9
--              in 
--                
--                  case x1
--                    of nil => x3 x0
--                     | :: x13 => 
--                         let
--                           val (x14, x15): 'a * 'a list = x13
--                         in 
--                           x6 (x10, x11, x14, x15)
--                         end
--              end
--   end

*)

fun merge xs [] = xs 
  | merge [] ys = ys 
  | merge (x::xs) (y::ys) = x::y::merge xs ys