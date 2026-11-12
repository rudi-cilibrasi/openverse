# expect: cannot infer type parameter t of Get
IntId(X:int)<computes>:int=X
box(t:type):=class<computes>{}
Get(?X:[]t=array{} where t:type)<computes>:box(t)=box(t){}
One(P:tuple(u) where u:type)<computes>:u=P(0)
holder:=class:
    F:type{_(:int)<computes>:int}=IntId
    Run():void=
        R:int=One(F(One(F(One(F(One(F(One(F(One(F(One(F(One(F(One(F(One(F(One(F(One(F(One(F(One(F(One(F(One(F(One(F(One(F(One(F(One(F(One(F(One(F(One(F(One(F(Get()))))))))))))))))))))))))))))))))))))))))))))))))
        Print("{R}")
Main():void=holder{}.Run()
