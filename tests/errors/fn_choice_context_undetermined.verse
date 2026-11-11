# expect: cannot infer the type parameters of Map
Id(X:t where t:type)<computes>:t=X
Map(F:type{_(:a)<computes>:b},X:a where a:type,b:type)<computes>:b=F(X)|F(X)
Main():void=
    R:=for{Map(Id,7)}
