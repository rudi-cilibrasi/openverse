# A break in a for's body leaves the loop around the for, and the for with
# it (#724): the Book's tests, Bugs/SOL-4199-BreakFromIf.versetest:39 ("`break`
# in a `for` body is allowed and breaks the surrounding `loop`"), and Epic's
# compiler and Verse VM (UEFN 43.12, followup-refused/break-in-for-in-loop).
# The defers of the scopes it leaves run, innermost first; a for whose value
# is being made is abandoned; the innermost loop is the one left. A for in
# no loop has nothing to leave (errors/break_outside_loop), nor does a break
# leave a for's clauses (errors/jump_break_for_clause).
int_ref := class:
    var Contents:int = 0
F(X:int_ref)<transacts><decides>:void =
    set X.Contents = 1
Twice(N:int):int = N | N + 10
Find(Xs:[]int, T:int):int =
    var At:int = -1
    loop:
        for (I -> X : Xs):
            if (X = T):
                set At = I
                break
        break
    At
Wait(N:int)<suspends>:int =
    Sleep(0.0)
    N
Susp()<suspends>:void =
    var N:int = 0
    loop:
        for (I := 1..5):
            set N += Wait(I)
            if (N > 3) then break
        Print("not reached")
        break
    Print("susp {N}")
Main()<suspends>:void =
    # the Book's case: a break in a for's body leaves the loop around it
    X := int_ref{}
    loop:
        for:
            I := 1..2
            F[X]
        do:
            break
        break
    Print("contents {X.Contents}")
    Print("find {Find(array{5, 6, 7}, 6)} {Find(array{5, 6, 7}, 9)}")
    # defers of the scopes it leaves run, innermost first
    var Rounds:int = 0
    loop:
        defer:
            Print("loop body defer")
        set Rounds += 1
        for (I := 1..3):
            defer:
                Print("for body defer {I}")
            if (I = 2, Rounds = 2) then break
        Print("round {Rounds} done")
    Print("rounds {Rounds}")
    # nested fors, a filter, and a for whose value is used
    var Seen:[]int = array{}
    loop:
        Ys := for (A := 1..3, B := 1..3, A <> B):
            set Seen += array{10 * A + B}
            if (A = 2, B = 3) then break
            A
        Print("never {Ys.Length}")
        break
    Print("seen {Seen.Length}")
    # the inner loop is the one a break leaves
    var K:int = 0
    loop:
        for (I := 1..3):
            loop:
                set K += 1
                break
        break
    Print("k {K}")
    # choice in the clauses
    var C:int = 0
    loop:
        for (V := Twice(1) | Twice(2)):
            set C += V
            if (V > 5) then break
        break
    Print("c {C}")
    Susp()
    # in a map's for, and in a block inside the body
    var Keys:int = 0
    loop:
        for (Key -> Val : map{1 => "a", 2 => "b", 3 => "c"}):
            block:
                set Keys += Key
                if (Val = "b") then break
        break
    Print("keys {Keys}")
