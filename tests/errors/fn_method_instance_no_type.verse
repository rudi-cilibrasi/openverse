# expect: a function type determining all its method type arguments and satisfying its bounds must be expected
box:=class:
    Same(X:t where t:type):t=X
Main():void=
    F:=box{}.Same
    Print("wrong")
