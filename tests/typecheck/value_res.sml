(* value restriction. example from MLton

-- expected stdout:
-- 0 warnings, 1 errors

-- expected stderr:
-- Error
-- 35,9 Type unification: can't unify function with argument types
-- Type constructors differ: int, string

*)

datatype 'a option = Some of 'a | None
val 'a := = primitive "Assign" : 'a ref * 'a -> unit
val 'a ! = primitive "Deref" : 'a ref -> 'a

infix 3 := 

val f: 'a -> 'a =
   let
      val r: 'a option ref = ref None
   in
      fn x =>
      let
         val y = !r
         val () = r := (Some x)
      in
         case y of
            None => x
          | Some y => y
            end
      end
   end
val _ = f 13
val _ = f "foo"