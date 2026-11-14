# A first's generator over a value of a type parameter whose bound is an
# array or a map, as a for's (its view of the bound).
KeyOf(M:t where t:subtype([int]int))<transacts><decides>:int = first{K -> V : M; V > 15; K}
ValueOf(M:t where t:subtype([int]int))<transacts><decides>:int = first{V : M; V > 15; V}
At(A:t where t:subtype([]int))<transacts><decides>:int = first{I -> E : A; E > 15; I}
Main():void =
    M:[int]int = map{1 => 10, 2 => 10, 3 => 20}
    if (X := KeyOf[M]) then Print("key {X}")
    if (X := ValueOf[M]) then Print("value {X}")
    if (X := At[array{1, 20}]) then Print("index {X}")
