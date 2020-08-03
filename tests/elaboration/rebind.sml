(* rebinding of builtin data constructors is prohibited 

-- expected stdout:
-- 2 warnings, 2 errors

-- expected stderr:
-- Warn
-- 21,20 rebound data constructor: ::
-- 
-- Warn
-- 21,41 rebound data constructor: nil
-- 
-- Error
-- 21,20 builtin data constructor '::' cannot be rebound
-- 
-- Error
-- 21,41 builtin data constructor 'nil' cannot be rebound
-- 
*)

datatype 'a list = :: of 'a * 'a list | nil;