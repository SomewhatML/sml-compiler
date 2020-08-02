(* Test that the parser will issue a warning on top-level expression 
-- args: --v
-- expected stdout:
-- val _: int
-- 
-- 1 warnings, 0 errors

-- expected stderr:
-- Warn
-- 13,1 top level expressions are not supported! emitting `val _ = ...`
*)

if true then 1 else 0