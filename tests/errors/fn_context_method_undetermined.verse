# expect: cannot infer type parameter
box:=class:
    Same(X:t where t:type)<computes>:t=X
Map(F:type{_(:a)<computes>:b},X:a where a:type,b:type)<computes>:b=F(X)
Main():void=
    R:=Map(box{}.Same,7)
