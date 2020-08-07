(* 

-- args: --v
-- expected stdout:
-- val |>: 'a * 'a -> 'b -> 'b
-- val a: 'a * 'a -> 'b -> 'b
-- val b: 'a * 'a -> 'b -> 'b
-- val c: 'a * 'a -> 'b -> 'b
-- val |>: 'a * 'a -> 'b -> 'b
-- val m: 'a -> 'a
-- val u: 'a -> 'a
-- val x: int

*)

local
  local
    local
      fun |> (f, g) = g f
    in
      val a = |>; 
    end
  in
    val b = a; 
  end
in
  val c = b; 
end

val |> = c
infix 3 |>

val m = fn x => x
val u = fn x => x

val x = 10 |> m |> u