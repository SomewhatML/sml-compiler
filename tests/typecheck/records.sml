(* record types are sorted in unspecified, but fixed order
-- args: --v
-- expected stdout:
-- val x: {a: int, b: int, c: bool}
-- val y: {a: int, b: int, c: bool}
-- val test: {a: int, b: int, c: bool} -> (int, int)
*)

val x = {a = 10, b = 12, c = true}
val y = {b = 9, c = false, a = 11}

fun test {a=a:int, b=b:int, c=c:bool} = (a, b)