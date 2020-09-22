(* ensure that order of arguments in not changed during pre-flight match arm lifting

-- args: --vv --phase elab
-- expected stdout:
-- datatype 'a option = Some of 'a | None
-- val ('a, 'b) map = fn x2 => fn x3 => 
--   let
--     val x0 = fn x5 => 
--       let
--         val f: 'a -> 'b = #1 x5
--         val x: 'a = #2 x5
--       in 
--         Some f x
--       end
--     val x1 = fn x6 => None
--   in 
--     
--       case x2
--         of Some x7 => x0 (x3, x7)
--          | None => x1 ()
--   end

*)

datatype 'a option = Some of 'a | None 

fun map (Some x) f = Some (f x)
  | map None _ = None