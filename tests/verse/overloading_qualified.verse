# qualified implementations of overloaded methods (#125): (i:)M per overload, qualified calls stay qualified
i1 := interface:
    M(X:int):string
    M(X:string):string
i2 := interface:
    M(X:int):string
c := class(i1, i2):
    (i1:)M<override>(X:int):string = "i1 int {X}"
    (i1:)M<override>(X:string):string = "i1 string {X}"
    (i2:)M<override>(X:int):string = "i2 int {X}"
    Both():string = "{(i1:)M(1)} / {(i2:)M(2)} / {(i1:)M("s")}"
Main():void =
    C := c{}
    A:i1 = C
    B:i2 = C
    Print(A.M(1))
    Print(A.M("a"))
    Print(B.M(3))
    Print(C.(i1:)M(4))
    Print(C.(i2:)M(5))
    Print(C.(i1:)M("b"))
    Print(C.Both())
