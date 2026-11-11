# expect: a function type determining all its method type arguments and satisfying its bounds must be expected
box:=class:
    Same(X:t where t:type)<decides>:t=block{false?;X}
Run(X:u where u:type):void=
    F:type{_(:u):u}=box{}.Same
Main():void=Run(3)
