# 3582 follow-up (#724), compile only: a module constant defined with an
# operator the program overloads, `operator'+'` of a <computes> class, a
# function of the program's written as an operator (the built-in operators
# are admitted, div-const-operator). OpenVerse refuses it: "the value of the
# constant Sum calls operator'+', which might not complete" (3582). If Epic
# admits it, the run prints "sum 3".
vec := class<computes>:
    A:int = 0

operator'+'(L:vec, R:vec)<computes>:vec = vec{A := L.A + R.A}

Sum:vec = vec{A := 1} + vec{A := 2}

Main():void =
    Print("OVPROBE sum {Sum.A}")
