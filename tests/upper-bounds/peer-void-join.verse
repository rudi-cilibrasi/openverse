Join(X:u,Y:v where t:type,u:subtype(t),v:subtype(t))<computes>:t=X
Accept(X:any)<computes>:void={}
Main():void=
    A:any=7
    B:void=8
    R:=Join(A,B)
    S:=Join(B,A)
    T:=Join(array{A},array{B})
    U:=Join(array{B},array{A})
    Accept(R)
    Accept(S)
    Print("join {T.Length} {U.Length}")
