(* check that flexible records do not unify with a missing constraint

-- expected stdout:
-- 0 warnings, 1 errors 

-- expected stderr:
-- Error
-- 14,22 Type unification: pattern and expression have different types in `val` declaration
-- Flexible record constraint not in rigid record: {x: int, y: bool, c: string, d: int ref}, {x: int, y: bool, z: 'a, ... }

*)

val record = {x = 10, y = true, c = "hello", d = ref 10 };
val {x, y, z, ...} = record;