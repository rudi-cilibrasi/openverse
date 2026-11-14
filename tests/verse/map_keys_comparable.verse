# Map keys: comparable types, and no array or map inside them but strings
# (Book of Verse ch. 3).
point := struct{ X:int, Y:int }
box(t:type) := struct{ V:t }
Main():void =
    A:[string]int = map{"one" => 1}
    B:[tuple(int, ?int)]int = map{(1, false) => 2}
    C:[point]int = map{point{X := 1, Y := 2} => 3}
    D:[box(string)]int = map{box(string){V := "s"} => 4}
    if (V := A["one"], W := B[(1, false)], Z := C[point{X := 1, Y := 2}]) then Print("{V} {W} {Z}")
    if (Q := D[box(string){V := "s"}]) then Print("{Q}")
