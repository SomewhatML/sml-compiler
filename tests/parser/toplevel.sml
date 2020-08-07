(* Test that the parser will issue a warning on top-level expression 

-- args: --v
-- expected stdout:
-- 1 warnings, 0 errors
-- val x0: int

-- expected stderr:
-- Warn
-- 14,1 top level expressions are not supported! emitting `val _ = ...`

*)

if true then 1 else 0