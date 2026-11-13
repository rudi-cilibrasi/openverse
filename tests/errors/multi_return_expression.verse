# expect: 4:0: F has several values and a return inside an expression or a condition, which would leave its caller once inlined (#235, #283): return in an if's branch, a block or a case's arm
# (#283) A return in a binding's value is not taken out as one in an if's branch, a block or a
# case's arm is (a scope that ends the invocation).
F(X:int)<transacts>:int =
    Y := if (X > 2) then (return 0) else X * 10
    Y | Y + 1
Main()<transacts>:void =
    for (V := F(3)) { Print("a {V}") }
    for (V := F(1)) { Print("b {V}") }
