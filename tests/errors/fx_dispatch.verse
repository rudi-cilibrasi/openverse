# expect: Total calls circle.Area, which has the effect <writes>
shape := class<abstract>:
    var Hits:int = 0
    Area()<transacts>:int
square := class(shape):
    S:int
    Area<override>()<transacts>:int = S * S
circle := class(shape):
    R:int
    Area<override>()<transacts>:int =
        set Hits += 1
        3 * R * R
Total(Shapes:[]shape)<reads>:int =
    var T:int = 0
    for (S : Shapes) { set T += S.Area() }
    T
Main():void = Print("{Total(array{square{S := 1}, circle{R := 1}})}")
