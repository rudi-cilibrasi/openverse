# one overload implemented qualified, the other not (#125)
shape := class:
    N:int = 1
square := class(shape):
    M:int = 2
i := interface:
    M(X:int):int
    M(S:string):int
q := class(i):
    (i:)M<override>(X:int):int = 1
    M<override>(S:string):int = 2
Main():void =
    Q := q{}
    A:i = Q
    Print("{A.M(1)} {A.M("s")} {Q.(i:)M(3)}")
