# expect: a function type determining all its method type arguments and satisfying its bounds must be expected
root(t:type):=class:
    V:t
    Match(X:u,Y:u where u:subtype(comparable))<decides>:u=block{X=Y;X}
bounded(t:subtype(comparable)):=class(root(t)){}
Use(P:root(t) where t:type):void=
    if(D:=bounded[P]):
        F:type{_(:t,:t)<decides>:t}=D.Match
    else:
        F:type{_(:t,:t)<decides>:t}=P.Match
Main():void=Use(root(int){V:=3})
