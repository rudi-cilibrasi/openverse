# generic functions with several values consumed in generic functions (#235)
Pick(X:t, Y:t where t:type):t = X | Y
Elements(A:[]t, I:int where t:type)<decides>:t =
    I < A.Length
    A[I] | Elements[A, I + 1]
Both(X:t, Y:t where t:type):[]t = for (Z := Pick(X, Y)) { Z }
All(A:[]t where t:type):[]t = for (Z := Elements[A, 0]) { Z }
Main():void =
    Print("{Both(1, 2).Length} {All(array{"x", "y", "z"}).Length}")
