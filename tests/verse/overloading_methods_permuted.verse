# overloads of a parametric class's method, overridden in a subclass that permutes its type parameters (#106 review)
pair(t:type, u:type) := class:
    A:t
    B:u
    M(X:t):string = "pair t"
    M(S:string, N:int):string = "pair s"
swap(a:type, b:type) := class(pair(b, a)):
    M<override>(X:b):string = "swap b"
Main():void =
    S := swap(int, char){A := 'c', B := 1}
    Print(S.M('x'))
    Print(S.M("q", 1))
    P:pair(char, int) = S
    Print(P.M('y'))
