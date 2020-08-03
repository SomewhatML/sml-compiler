(* catch escaping datatypes

-- expected stdout:
-- 0 warnings, 1 errors

-- expected stderr:
-- Error
-- 16,5 type escapes scope: t

*)

val _ = 
  let
    datatype t = T of int
  in
    T 10
  end
