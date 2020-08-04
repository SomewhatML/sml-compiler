(* check that local declarations don't escape

-- expected stdout:
-- 0 warnings, 1 errors

-- expected stderr:
-- Error
-- 19,9 unbound variable: x

*)

local
  val x = 10
in 
  val y = x
end

val _ = y
val _ = x