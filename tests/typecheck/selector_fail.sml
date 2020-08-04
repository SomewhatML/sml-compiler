(* ensure record field selectors fail when used incorrectly

-- expected stdout:
-- 0 warnings, 2 errors

-- expected stderr:
-- Error
-- 17,9 Type unification: can't unify function with argument types
-- Flexible record constraint not in rigid record: int * bool, {3: 'a, ... }
-- 
-- Error
-- 19,9 Type unification: can't unify function with argument types
-- Flexible record constraint not in rigid record: {y: int, z: bool}, {x: 'a, ... }

*)

val _ = #3 (0, true)

val _ = #x {y=10, z=true}