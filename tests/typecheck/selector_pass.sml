(* ensure record field selectors unify

-- args: --v --phase elab
-- expected stdout:
-- val a: int
-- val b: bool
-- val c: {x: string} -> string
-- val d: string

*)

val a = #1 (0, true)

val b = #z {y=10, z=true}

(* immediately after this line, this has type {x: 'a, ...} -> 'a *)
val c = #x

(* since flex records aren't generalized, c will be unified to {x: string} -> string *)
val d = c {x = "hello" }