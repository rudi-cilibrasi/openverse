# expect: a function type determining all its method type arguments and satisfying its bounds must be expected
box:=class:
    Later(X:t where t:type)<suspends>:t=block{Sleep(0.0);X}
Run(X:u where u:type):void=
    F:type{_(:u):u}=box{}.Later
Main():void=Run(3)
