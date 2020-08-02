(* create a cyclic type 
-- expected stderr:
-- Error
-- 16,21 Cyclic type detected: 'i#1 interned symbol
-- 
-- Error
-- 16,5 Cyclic type detected: 'i#1 interned symbol

-- expected stdout:
-- 0 warnings, 2 errors
*) 


fun repeat x 0 = []
  | repeat x 1 = [x]
  | repeat x n = [x]::repeat x n
 