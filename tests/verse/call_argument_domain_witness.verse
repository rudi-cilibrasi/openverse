# One actual singleton tuple fits these separately named domains.
# Each corresponding overload pair must therefore be refused at admission.
Single(P:tuple(u) where u:type)<computes>:tuple(u)=P
Scalar(X:int)<computes>:int=X
Nested(P:tuple(tuple(int)))<computes>:int=P(0)(0)
Array(P:[]int)<computes>:int=P[0] or -1
Main():void=
    W:type{_(:int)<computes>:tuple(int)}=Single
    T:=W(7)
    Print("{Scalar(T)} {Nested(T)} {Array(T)}")
