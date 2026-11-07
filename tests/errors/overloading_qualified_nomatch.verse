# expect: 7:4: (i1:)M must have the parameters of one of i1's overloads of M
i1 := interface:
    M(X:int):string
    M(X:string):string
c := class(i1):
    (i1:)M<override>(X:int):string = "a"
    (i1:)M<override>(X:char):string = "b"
Main():void = Print("x")
