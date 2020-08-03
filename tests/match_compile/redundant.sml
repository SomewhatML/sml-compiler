(* give error on unreachable match arm 

-- expected stdout:
-- 0 warnings, 1 errors 

-- expected stderr:
-- Error
-- 14,15 unreachable match arm

*)

fun match 0 = 0
  | match 1 = 1
  | match 1 = 1
  | match n = n