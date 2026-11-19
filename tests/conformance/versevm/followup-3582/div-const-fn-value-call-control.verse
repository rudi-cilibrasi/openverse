# 3582 follow-up (#724), control of div-const-fn-value-call: a module
# constant that names a <computes> function as a value, which calls
# nothing, and a call of it in a function. OpenVerse admits it and prints
# "two 2".
Next(X:int)<computes>:int = X + 1

Step:type{_(:int)<computes>:int} = Next

Main():void =
    Print("OVPROBE two {Step(1)}")
