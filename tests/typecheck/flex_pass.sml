(* check that flexible records unify with a rigid record 

-- args: --v
-- expected stdout:
-- val record: {x: int, y: bool, c: string, d: int ref}
-- val {x= x, y= y}: {x: int, y: bool, c: string, d: int ref}

*)

val record = {x = 10, y = true, c = "hello", d = ref 10 };
val {x, y, ...} = record;