(* rebinding of builtin data constructors is prohibited 

-- expected stdout:
-- 0 warnings, 1 errors

-- expected stderr:
-- Error
-- 12,11 duplicate variable in pattern, emitting bogus value

*)

fun dup x x = x