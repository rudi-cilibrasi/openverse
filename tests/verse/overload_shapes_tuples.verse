# Pinned tuple/container distinctness, with actual calls to each domain.
a := class:
    N:int = 3
b := class:
    N:int = 7
One(X:tuple(t) where t:type)<computes>:tuple(t) = X
M(X:tuple(a), Tag:a):string = "tuple {X(0).N}"
M(X:[logic]a, Tag:a):string = "map {X.Length}"
O(X:?a, Tag:a):string = "option"
O(X:tuple(a), Tag:a):string = "tuple {X(0).N}"
A(X:tuple(a,b), Tag:a):string = "tuple {X(0).N} {X(1).N}"
A(X:[]a, Tag:a):string = "array {X.Length}"
Main():void =
    Pack:type{_(:a)<computes>:tuple(a)} = One
    V := a{}
    T := Pack(V)
    Print(M(T,V))
    Print(M(map{true=>V},V))
    Print(O(T,V))
    Print(O(option{V},V))
    Print(A((V,b{}),V))
    Print(A(array{V,V},V))
