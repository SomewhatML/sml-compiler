(* check that generalization of flexible records fails

-- expected stdout:
-- 0 warnings, 1 errors

-- expected stderr:
-- Error
-- 16,9 Type unification: can't unify function with argument types
-- Record types have differing number of fields: {x: int, y: bool, z: string}, {x: int, y: bool, z: string, e: bool}

*)

fun m {x, y, ...} = (x, y)

val x = m {x=10, y=true, z="hello"}
val y = m {x=10, y=true, z="goodbye", e=true}