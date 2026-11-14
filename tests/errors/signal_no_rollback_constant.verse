# expect: 8:13: the value of the constant K calls Fresh, which has the effect <writes>: a module's constant has no side effect
# (#515) under --signal-no-rollback, a use of a constant in an if's condition
# runs its initialiser, which signals
Fresh():int =
    E := event(int){}
    E.Signal(1)
    1
K:int = Fresh()
Main():void =
    if (K > 2) then Print("no") else Print("else")
