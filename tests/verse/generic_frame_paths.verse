# A generic callee's frame sits in a field of type `ref [callee, $nil] args`
# and is resumed after a test of its class, outside any condition (#256):
# made on the first call, reset on the next ones (a loop), resumed with its
# parameters from itself, cancelled with its defers (a task cancelled while
# it waits there, a race's loser), and its result taken through `g$result`;
# the same for a generic override dispatched to under a refinement.
Pause(X:t, N:int where t:type)<suspends>:t =
    defer:
        Print("pause {N} unwound")
    Sleep(1.0)
    X

Twice(X:t where t:type)<suspends>:tuple(t, t) =
    A := Pause(X, 1)
    B := Pause(X, 2)
    (A, B)

Loop(X:t, N:int where t:type)<suspends>:int =
    var Sum:int = 0
    for (I := 1..N):
        Pause(X, 10 + I)
        set Sum += I
    Sum

Slow(X:t where t:type)<suspends>:t =
    defer:
        Print("slow unwound")
    Sleep(5.0)
    X

Fast(X:t where t:type)<suspends>:t =
    Sleep(1.0)
    X

pair(a:type, b:type) := class:
    A:a
    B:b
    Both(X:b)<suspends>:tuple(a, b) = (A, X)
ipair(b:type) := class(pair(int, b)):
    Both<override>(X:b)<suspends>:tuple(int, b) =
        defer:
            Print("ipair both unwound")
        Sleep(1.0)
        (A * 10, X)

# a generic override, dispatched to by a test of the receiver's class
Use(P:pair(a, b), Y:b, N:int where a:type, b:type)<suspends>:a =
    var R:a = P.A
    for (I := 1..N):
        set R = P.Both(Y)(0)
    R

Main()<suspends>:void =
    P := Twice(7)
    Print("twice {P(0)} {P(1)}")
    Print("loop {Loop("a", 3)}")
    T := spawn{Slow(1)}
    Sleep(2.0)
    T.Cancel()
    Print("cancelled")
    W := race:
        Slow(2)
        Fast(3)
    Print("race {W}")
    Print("use {Use(ipair(string){A := 4, B := "x"}, "y", 2)}")
    U := spawn{Use(ipair(logic){A := 5, B := true}, false, 3)}
    Sleep(1.5)
    U.Cancel()
    Print("use cancelled")
