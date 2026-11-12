A(P:tuple(void))<computes>:string="tuple"
B(P:[logic]void)<computes>:string="map"
Cmp(X:t where t:subtype(comparable))<computes>:int=7
Main():void=
    M:[logic]void=map{true=>()}
    Print("bound {Cmp(())}")
    Print(A(M))
    Print(B(M))
