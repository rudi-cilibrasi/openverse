# expect: FindSingle has several values and a return in a loop or binding initializer whose expression is not single-valued or starts concurrent work: not supported yet (#686, #687)
# Two unrelated classes declare `Vals`, and the receiver's class is the one
# whose `Vals` has one value: its call stays a method's, so the `for` has no
# clause with several values and its return of several is refused, as it is
# when the method's name is its class's alone. (Over `left`'s, which has
# several, the loop is supported: tests/verse/loop_return_shared_method_name.)
left := class:
    Vals()<transacts>:int = 4 | 1
single := class:
    Vals()<transacts>:int = 5
FindSingle(S:single)<transacts>:int =
    for (V := S.Vals()):
        return V | V + 10
    0
Main()<transacts>:void =
    for (X := FindSingle(single{})):
        Print("single {X}")
    for (X := left{}.Vals()):
        Print("left {X}")
