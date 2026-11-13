Id(X:t where t:type)<computes>:t=X
UseGlobal():int=block{F:type{_(:int)<computes>:int}=Id;F(1)}
Local(X:int)<computes>:int=X+1
Echo(F:type{_(:a)<computes>:b},X:a where a:type,b:type)<computes>:b=F(X)|F(X)
box:=class:
    (box:)Id:type{_(:int)<computes>:int}
    Run():[]int=for{Echo((box:)Id,7)}
Shadow(Id:type{_(:int)<computes>:int}):[]int=for{Echo(Id,3)}
Main():void=
    R:=Shadow(Local)
    S:=box{Id:=Local}.Run()
    for(N:R):Print("{N}")
    for(N:S):Print("{N}")
