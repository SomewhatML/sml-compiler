(* check that two flexible record patterns won't unify with each other

-- expected stdout:
-- 0 warnings, 1 errors

-- expected stderr:
-- Error
-- 15,10 Type unification: function clause with argument of different type
-- Can't unify these types: {x: int, y: int, ... }, {x: int, y: int, ... }

*)


fun flex {x, y=10, ... } = (x, 10)
  | flex {x=10, y, ... } = (10, y)
  | flex _               = (0, 0)