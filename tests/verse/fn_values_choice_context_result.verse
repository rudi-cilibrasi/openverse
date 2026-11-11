Empty(N:int where t:type)<computes>:[]t=array{}
Twice(F:type{_(:int)<computes>:[]t},X:t where t:type)<computes>:int=F(0).Length|F(1).Length
Run(X:t where t:type)<computes>:[]int=for{Twice(Empty,X)}
Main():void=
    R:=Run("s")
    Print("{R.Length}")
    for(N:R):Print("{N}")
