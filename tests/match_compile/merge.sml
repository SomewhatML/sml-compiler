(* test pattern match compilation to decision trees

-- args: --vv
-- expected stdout:
-- val 'a merge: 'a list -> 'a list -> 'a list = fn a => fn b => 
--   let
--     val e: 'a list -> 'a list = fn d => 
--       let
--         val xs: 'a list = d
--       in 
--         xs
--       end
--     val g: 'a list -> 'a list = fn f => 
--       let
--         val ys: 'a list = f
--       in 
--         ys
--       end
--     val i: 'a * 'a list * 'a * 'a list -> 'a list = fn h => 
--       let
--         val (x, xs, y, ys): 'a * 'a list * 'a * 'a list = h
--       in 
--         :: (x, :: (y, merge xs ys))
--       end
--   in 
--     
--       case a
--         of nil => 
--           case b
--             of nil => e a
--              | _ => g b
--          | :: l => 
--              let
--                val (m, n): 'a * 'a list = l
--              in 
--                
--                  case b
--                    of nil => e a
--                     | :: p => 
--                         let
--                           val (q, r): 'a * 'a list = p
--                         in 
--                           i (m, n, q, r)
--                         end
--              end
--   end

*)

fun merge xs [] = xs 
  | merge [] ys = ys 
  | merge (x::xs) (y::ys) = x::y::merge xs ys