First(X:any,Y:void)<computes>:any=X
Second(X:void,Y:any)<computes>:any=X
FirstArray(X:[]any,Y:[]void)<computes>:[]any=X
SecondArray(X:[]void,Y:[]any)<computes>:[]any=X
Accept(X:any)<computes>:void={}
Main():void=
    A:any=7
    B:void=8
    R:=First(A,B)
    S:=Second(B,A)
    T:=FirstArray(array{A},array{B})
    U:=SecondArray(array{B},array{A})
    Accept(R)
    Accept(S)
    Print("join {T.Length} {U.Length}")
