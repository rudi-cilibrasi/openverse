# an overload's own type parameter named like the class's argument (#106 review)
box(t:type) := class:
    V:t
    M(X:t, Y:u where u:type):string = "box"
    M(X:int, Y:int):string = "box ii"
sub(u:type) := class(box(u)):
    M<override>(X:u, Y:w where w:type):string = "sub"
Main():void =
    B:box(string) = sub(string){V := "a"}
    Print(B.M("x", 1))
