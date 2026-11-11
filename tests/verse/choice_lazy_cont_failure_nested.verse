# Each nested lazy producer forwards a failed continuation outcome.
counter := class:
    var N:int = 0
Two(N:int):int = N | N + 1
Lazy(C:counter, N:int)<transacts><decides>:int =
    N >= 0
    set C.N += 1
    N | Lazy[C, N - 1]
Main()<decides>:void =
    C := counter{}
    R := for (A := (Two(0) | Two(2)), X := 1..2, L := Lazy[C, 0], M := Lazy[C, 0], B := (Two(0) | Two(2)), D := (Two(0) | Two(2))):
        Print("body {A} {X} {L} {M} {B} {D} visits {C.N}")
        false?
        B
    Print("unreachable {R.Length}")
