# an override matched to its overload through the type arguments its class gives its parent (#106 review)
pair(t:type, u:type) := class:
    A:t
    B:u
    M(?X:t):string = "pair t"
    M(X:int, Y:int):string = "pair ii"
    M(X:u, Y:string):string = "pair us"
swap(a:type, b:type) := class(pair(b, a)):
    M<override>(?X:b):string = "swap b"
    M<override>(X:a, Y:string):string = "swap as"
Main():void =
    S := swap(int, char){A := 'c', B := 1}
    Print(S.M(?X:='x'))
    Print(S.M(1, "s"))
    Print(S.M(1, 2))
