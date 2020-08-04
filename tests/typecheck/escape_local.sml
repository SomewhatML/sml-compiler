(* check that local declarations don't escape

-- expected stdout:
-- 0 warnings, 1 errors

-- expected stderr:
-- Error
-- 15,7 type escapes scope: t

*)

local
  datatype t = T of int
in 
  val y = T 10
end

val _ = y