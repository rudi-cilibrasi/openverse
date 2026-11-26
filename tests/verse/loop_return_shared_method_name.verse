# (#686) A loop return of several values from a `for` whose clauses call a
# method whose name two unrelated classes declare, neither overriding the
# other's. Which class's method `R.Vals()` calls is told by `R`'s class,
# which the first elaboration notes; until then the call is as written, and
# the loop was refused for it: "a return in a loop or binding initializer
# whose expression is not single-valued". The function now waits for that
# elaboration, and the call is then the one implementation's, as it is when
# one class has the name.
#
# `left`'s Vals gives 4 then 1, `right`'s 7 then 8, and `single`'s the one
# value 5. Each control has the same clauses and no return: its rows are an
# array, whose first is the row the return is reached in.
left := class:
    Vals()<transacts>:int = 4 | 1
    Scale(K:int)<transacts>:int = K | K * 2
    # In a method, over the other class's: the first over 7 is 8. 8, 18.
    SeekOther(R:right)<transacts>:int =
        for (V := R.Vals(), V > 7):
            return V | V + 10
        0
right := class:
    Vals()<transacts>:int = 7 | 8
    Scale(K:int)<transacts>:int = K * 3 | K * 4
single := class:
    Vals()<transacts>:int = 5
Cell := class{var N:int = 0}
Tick(S:Cell, K:int)<transacts>:int =
    set S.N += 10
    Print("tick {K}")
    K
# The first row returns: 4, 14.
FindLeft(L:left)<transacts>:int =
    for (V := L.Vals()):
        return V | V + 10
    0
LeftRows(L:left)<transacts>:[]int =
    for (V := L.Vals()):
        V
# The other class's method, in a loop of its own: 7, 17.
FindRight(R:right)<transacts>:int =
    for (V := R.Vals()):
        return V | V + 10
    0
RightRows(R:right)<transacts>:[]int =
    for (V := R.Vals()):
        V
# The class whose method has one value: its call stays a method's. I = 1
# has V = 5: 5, 6.
FindSingle(S:single)<transacts>:int =
    for (I := 1..3):
        if (V := S.Vals(), V = I + 4):
            return V | V + 1
    0
# Both in one function, each in a loop of its own. `left` has no value over
# 5, so its loop ends; `right`'s first is 7: 7, 70.
FindBoth(L:left, R:right)<transacts>:int =
    for (V := L.Vals(), V > 5):
        return V | V + 100
    for (W := R.Vals(), W > 5):
        return W | W * 10
    0
# Both in one header. The rows are (4, 7), (4, 8), (1, 7), (1, 8); the first
# with V + W = 9 is (1, 8): 18, 81.
FindPair(L:left, R:right)<transacts>:int =
    for (V := L.Vals(), W := R.Vals(), V + W = 9):
        return V * 10 + W | W * 10 + V
    0
PairRows(L:left, R:right)<transacts>:[]int =
    for (V := L.Vals(), W := R.Vals(), V + W = 9):
        V * 10 + W
# A generator before the call, and a filter after it. W = 1 has no V with
# V + W = 3; W = 2 has V = 1: 12, 0.
FindAfter(L:left)<transacts>:int =
    for (W := 1..2, V := L.Vals(), V + W = 3):
        return V * 10 + W | 0
    0
AfterRows(L:left)<transacts>:[]int =
    for (W := 1..2, V := L.Vals(), V + W = 3):
        V * 10 + W
# An argument with an effect. `right` gives 15 then 20, and 20 is over 15:
# 20, 21, after one `tick 5`, and S.N is 10. `left` gives 5 then 10, so no
# row reaches the body: nothing is printed, S.N stays 0, and the value is 0.
FindArgs(S:Cell, R:right)<transacts>:int =
    for (V := R.Scale(Tick(S, 5)), V > 15):
        return V | V + 1
    0
FindArgsLeft(S:Cell, L:left)<transacts>:int =
    for (V := L.Scale(Tick(S, 5)), V > 15):
        return V | V + 1
    0
# A `defer:` in the body: each returned value runs it before it is given.
FindDefer(L:left)<transacts>:int =
    for (V := L.Vals()):
        defer:
            Print("defer {V}")
        return V | V + 10
    0
# A return of one value, in the row that has V = 1: the row before it falls
# through, and the values after the loop are not reached. 1.
FindIf(L:left)<transacts>:int =
    for (V := L.Vals()):
        if (V = 1):
            return V
    7 | 8
# In a `loop`, after a `for` over the other class's that does not return.
# N = 4 + 1 = 5, and `right`'s first over 5 is 7: 7, 17. (The `break` is
# never taken: it gives the loop an end that is not a return.)
FindLoop(L:left, R:right)<transacts>:int =
    var N:int = 0
    loop:
        for (V := L.Vals()):
            set N += V
        for (W := R.Vals(), W > N):
            return W | W + 10
        if (N > 100):
            break
    0
# A generic function, at two instances: 4, 14 each.
FindGeneric(L:left, Extra:t where t:type)<transacts>:int =
    for (V := L.Vals()):
        return V | V + 10
    0
Main()<transacts>:void =
    for (X := FindLeft(left{})):
        Print("left {X}")
    for (X : LeftRows(left{})):
        Print("left row {X}")
    for (X := FindRight(right{})):
        Print("right {X}")
    for (X : RightRows(right{})):
        Print("right row {X}")
    for (X := FindSingle(single{})):
        Print("single {X}")
    for (X := FindBoth(left{}, right{})):
        Print("both {X}")
    for (X := FindPair(left{}, right{})):
        Print("pair {X}")
    for (X : PairRows(left{}, right{})):
        Print("pair row {X}")
    for (X := FindAfter(left{})):
        Print("after {X}")
    for (X : AfterRows(left{})):
        Print("after row {X}")
    S1 := Cell{}
    for (X := FindArgs(S1, right{})):
        Print("args {X}")
    Print("args state {S1.N}")
    S2 := Cell{}
    for (X := FindArgsLeft(S2, left{})):
        Print("args left {X}")
    Print("args left state {S2.N}")
    for (X := FindDefer(left{})):
        Print("defer found {X}")
    if (X := FindDefer(left{}), X = 14):
        Print("defer first {X}")
    for (X := FindIf(left{})):
        Print("in if {X}")
    for (X := left{}.SeekOther(right{})):
        Print("seek other {X}")
    for (X := FindLoop(left{}, right{})):
        Print("in loop {X}")
    for (X := FindGeneric(left{}, "s")):
        Print("generic string {X}")
    for (X := FindGeneric(left{}, 3)):
        Print("generic int {X}")
