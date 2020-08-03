(* give error on exhaustive case expression

-- expected stdout:
-- 0 warnings, 1 errors

-- expected stderr:
-- Error
-- 13,14 inexhaustive `case` expression

*)

val x = 10
val y = case x 
  of 1 => true
   | 2 => false
   | 3 => true 
   | 4 => false 
end