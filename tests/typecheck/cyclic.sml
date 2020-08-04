(* create a cyclic type 

-- expected stderr:
-- Error
-- 20,21 Type unification: can't unify function with argument types
-- Cyclic type detected: 'a list, 'a
-- 
-- Error
-- 20,5 Type unification: function clause body doesn't match with return type
-- Cyclic type detected: 'a, 'a list

-- expected stdout:
-- 0 warnings, 2 errors

*) 


fun repeat x 0 = []
  | repeat x 1 = [x]
  | repeat x n = [x]::repeat x n
 