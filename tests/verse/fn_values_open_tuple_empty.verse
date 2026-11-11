Const(where t:type)<computes>:[]t=array{}
Empty(P:tuple() where t:type)<computes>:[]t=array{}
Run(X:t where t:type)<computes>:int=
    F:type{_(:tuple())<computes>:[]t}=Const
    G:type{_()<computes>:[]t}=Empty
    F(()).Length+G().Length
Main():void=Print("{Run(3)} {Run("s")}")
