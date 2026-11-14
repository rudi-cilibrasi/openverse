Empty(N:t where t:type)<computes>:[]t=array{}
Twice(F:type{_(:t)<computes>:[]t},X:t where t:type)<computes>:int=F(X).Length|F(X).Length
Run(X:t where t:type)<computes>:[]int=for{Twice(Empty,X)}
Main():void=
    R:=Run("s")
    Print("{R.Length}")
    for(N:R):Print("{N}")
