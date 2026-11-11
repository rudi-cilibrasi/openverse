# expect: a function type determining all its method type arguments and satisfying its bounds must be expected
box:=class:
    Same(X:t,Y:t where t:subtype(comparable))<decides>:t=block{X=Y;X}
Run(X:u where u:type):void=
    F:type{_(:u,:u)<decides>:u}=box{}.Same
Main():void=Run(3)
