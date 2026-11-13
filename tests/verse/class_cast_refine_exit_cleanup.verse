# Explicit exits preserve their operand and copy locals after branch cleanup.
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 7
Returns(P:pair(a, b) where a:type, b:type):int =
    var Value:int = 0
    defer: Print("return cleanup saw {Value}")
    if (D := dup[P]):
        defer: set Value = 9
        set Value = D.C
        return Value
    0
ReturnsVoid(P:pair(a, b) where a:type, b:type):void =
    var Value:int = 0
    defer: Print("void cleanup saw {Value}")
    if (D := dup[P]):
        defer: set Value = 9
        set Value = D.C
        return
    Print("void miss")
Breaks(P:pair(a, b) where a:type, b:type):void =
    var Value:int = 0
    loop:
        if (D := dup[P]):
            defer: set Value = 9
            set Value = D.C
            break
        break
    Print("break left {Value}")
NestedReturn(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type):int =
    var Value:int = 0
    var Other:int = 0
    defer: Print("nested return left {Value}, {Other}")
    if (D := dup[P]):
        defer:
            set Value += 100
            set Other += Value
            Print("outer cleanup {Value}, {Other}")
        if (E := dup[Q]):
            defer:
                set Value += 10
                set Other += Value
                Print("inner cleanup {Value}, {Other}")
            set Value = E.C
            return Value
    -1
NestedBreak(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type):void =
    var Value:int = 0
    loop:
        defer: Print("loop cleanup {Value}")
        if (D := dup[P]):
            defer: set Value += 100
            if (E := dup[Q]):
                defer: set Value += 10
                set Value = E.C
                break
            set Value = 3
        break
    Print("nested break left {Value}")
ContainedBreak(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type):int =
    var Value:int = 0
    if (D := dup[P]):
        defer: set Value += 100
        loop:
            defer: set Value += 1
            if (E := dup[Q]):
                defer: set Value += 10
                set Value = E.C
                break
            break
        set Value += 1000
    Value
RefinedReturn(P:pair(a, b) where a:type, b:type):b =
    var Count:int = 0
    defer: Print("refined cleanup {Count}")
    if (D := dup[P]):
        defer: set Count = 9
        set Count = D.C
        return D.A
    P.B
# (a <decides> function's return is in tail position, a branch of its last if,
# Return.versetest:157)
DecidesReturn(P:pair(a, b), Values:[]int where a:type, b:type)<decides>:int =
    var Value:int = 0
    defer: Print("decides cleanup {Value}")
    if (D := dup[P]):
        defer: set Value = 9
        set Value = D.C
        return Values[Value]
    else:
        -1
Main():void =
    P := dup(int){A := 1, B := 2}
    Q := dup(string){A := "a", B := "b"}
    Miss := pair(int, string){A := 1, B := "miss"}
    Print("returned {Returns(P)}")
    Print("returned {Returns(Miss)}")
    ReturnsVoid(P)
    Breaks(P)
    Print("nested returned {NestedReturn(P, Q)}")
    Print("nested returned {NestedReturn(P, Miss)}")
    NestedBreak(P, Q)
    NestedBreak(P, Miss)
    Print("contained {ContainedBreak(P, Q)}")
    Print("refined {RefinedReturn(Q)}")
    if (V := DecidesReturn[P, array{10, 11, 12, 13, 14, 15, 16, 17}]):
        Print("decides {V}")
    if (V := DecidesReturn[P, array{10}]):
        Print("unexpected {V}")
    else:
        Print("return failed")
