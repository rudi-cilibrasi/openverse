# (#764) A loop return of several values with a call of an overridden method
# among the `for`'s other clauses. The receiver and the arguments are
# evaluated once, in order, before the implementation is picked, and they
# are clauses like the others: a row that reaches the body keeps what they
# did, and a `for` with no such row undoes it. Each control has the same
# clauses and no return: its rows are an array, whose first is the row the
# return is reached in.
#
# `derived`'s Vals gives 3 then 2, `base`'s 4 then 1; `derived`'s Scale(K)
# gives 3K then 4K, `base`'s K then 2K.
Cell := class{var N:int = 0}
base := class:
    Vals()<transacts>:int = 4 | 1
    Scale(K:int)<transacts>:int = K | K * 2
derived := class(base):
    Vals<override>()<transacts>:int = 3 | 2
    Scale<override>(K:int)<transacts>:int = K * 3 | K * 4
Pick(S:Cell, B:base)<transacts>:base =
    set S.N += 1
    Print("pick")
    B
Tick(S:Cell, K:int)<transacts>:int =
    set S.N += 10
    Print("tick {K}")
    K
# A receiver with an effect. V = 3 is not under 3, V = 2 is: 2, 12, after
# one `pick`, and S.N is 1.
Effect(S:Cell, B:base)<transacts>:int =
    for (V := Pick(S, B).Vals(), V < 3):
        return V | V + 10
    0
EffectRows(S:Cell, B:base)<transacts>:[]int =
    for (V := Pick(S, B).Vals(), V < 3):
        V
# The receiver, then the argument. A `derived` gives 15 then 20: 20, 21
# after `pick`, `tick 5`, and S.N is 11. A `base` gives 5 then 10, so no row
# reaches the body: nothing is printed, S.N stays 0, and the value is 0.
Args(S:Cell, B:base)<transacts>:int =
    for (V := Pick(S, B).Scale(Tick(S, 5)), V > 15):
        return V | V + 1
    0
ArgsRows(S:Cell, B:base)<transacts>:[]int =
    for (V := Pick(S, B).Scale(Tick(S, 5)), V > 15):
        V
# The receiver bound by an earlier clause, a generator. Over a `base` then
# a `derived`, the rows have V = 4, 1, 3, 2: K = 1..4 each find theirs, and
# K = 5 none.
Earlier(Bs:[]base, K:int)<transacts>:int =
    for (R : Bs, V := R.Vals(), V = K):
        return V | V + 10
    0
EarlierRows(Bs:[]base, K:int)<transacts>:[]int =
    for (R : Bs, V := R.Vals(), V = K):
        V
# The call in a branch of an `if`: 3, 13 when the flag holds, else 7, 17.
Branch(B:base, Flag:logic)<transacts>:int =
    for (V := if (Flag?) then B.Vals() else 7):
        return V | V + 10
    0
BranchRows(B:base, Flag:logic)<transacts>:[]int =
    for (V := if (Flag?) then B.Vals() else 7):
        V
# A generator after the call. The rows with V + W = 4 are (3, 1), (2, 2):
# 31, 0.
After(B:base)<transacts>:int =
    for (V := B.Vals(), W := 1..2, V + W = 4):
        return V * 10 + W | 0
    0
AfterRows(B:base)<transacts>:[]int =
    for (V := B.Vals(), W := 1..2, V + W = 4):
        V * 10 + W
# A generator before the call: W = 1 has (3, 1), W = 2 has (2, 2). 31, 0.
Before(B:base)<transacts>:int =
    for (W := 1..2, V := B.Vals(), V + W = 4):
        return V * 10 + W | 0
    0
BeforeRows(B:base)<transacts>:[]int =
    for (W := 1..2, V := B.Vals(), V + W = 4):
        V * 10 + W
Main()<transacts>:void =
    S1 := Cell{}
    for (X := Effect(S1, derived{})):
        Print("effect {X}")
    Print("effect state {S1.N}")
    S2 := Cell{}
    for (X : EffectRows(S2, derived{})):
        Print("effect row {X}")
    Print("effect rows state {S2.N}")
    S3 := Cell{}
    for (X := Args(S3, derived{})):
        Print("args {X}")
    Print("args state {S3.N}")
    S4 := Cell{}
    for (X : ArgsRows(S4, derived{})):
        Print("args row {X}")
    Print("args rows state {S4.N}")
    S5 := Cell{}
    for (X := Args(S5, base{})):
        Print("args base {X}")
    Print("args base state {S5.N}")
    S6 := Cell{}
    for (X : ArgsRows(S6, base{})):
        Print("args base row {X}")
    Print("args base rows state {S6.N}")
    Bs:[]base = array{base{}, derived{}}
    for (K := 1..5):
        for (X := Earlier(Bs, K)):
            Print("earlier {K}: {X}")
        for (X : EarlierRows(Bs, K)):
            Print("earlier row {K}: {X}")
    for (X := Branch(derived{}, true)):
        Print("branch true {X}")
    for (X : BranchRows(derived{}, true)):
        Print("branch true row {X}")
    for (X := Branch(derived{}, false)):
        Print("branch false {X}")
    for (X : BranchRows(derived{}, false)):
        Print("branch false row {X}")
    for (X := After(derived{})):
        Print("after {X}")
    for (X : AfterRows(derived{})):
        Print("after row {X}")
    for (X := Before(derived{})):
        Print("before {X}")
    for (X : BeforeRows(derived{})):
        Print("before row {X}")
