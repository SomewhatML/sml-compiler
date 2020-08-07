(*

-- args: --v --phase elab
-- expected stdout:
-- val m: 'a -> 'b
-- val n: 'a -> 'b

*)

fun m x = n x
and n x = m x