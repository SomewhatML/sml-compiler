(* check that flexible records unify with a rigid record 

-- args: --v --phase elab
-- expected stdout:
-- val record: {x: int, y: bool, c: string, d: int ref}
-- val x2: int * bool
-- val x: int
-- val y: bool

*)

val record = {x = 10, y = true, c = "hello", d = ref 10 };
val {x, y, ...} = record;