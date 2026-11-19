# 3582 follow-up (#724), compile only: a module constant defined by a call
# through a function value, another module constant that names a
# <computes> function (div-const-fn-value-call-control has that constant
# alone). OpenVerse refuses it: "the value of the constant Two calls a value
# of type type{_(:int)<computes>:int}, which might not complete" (3582).
# If Epic admits it, the run prints "two 2".
Next(X:int)<computes>:int = X + 1

Step:type{_(:int)<computes>:int} = Next

Two:int = Step(1)

Main():void =
    Print("OVPROBE two {Two}")
