# A break in the first-success clauses of an if, first{} or option{} with a
# choice leaves the nearest loop around them (#283); a loop of the clauses'
# own keeps its breaks, and so does a for's filter around the if.
Main()<transacts>:void =
    # nested loops: the inner one is left, the outer one goes on
    var I:int = 0
    loop:
        defer: Print("outer cleanup {I}")
        set I += 1
        loop:
            defer: Print("inner cleanup {I}")
            if (X := I | 9, X = 9, break) then Print("not reached")
            Print("not reached")
        Print("outer {I}")
        if (I = 2) then break
    # a loop in the clauses keeps its own break
    loop:
        if (X := 1 | 2, Y := block{ var K:int = 0; loop { set K += 1; if (K = 3) then break }; K + X }, Y = 5, Print("Y={Y}"), break):
            Print("not reached")
    # first{}: the first success of its clauses, the last its value
    var V:int = 0
    loop:
        if (Z := first{ X := 4 | 5 | 6; set V += X; X > 4; if (X = 5) then break else 0; X }) then Print("not reached")
        Print("not reached")
    Print("first: V={V}")
    loop:
        if (Z := first{ X := 4 | 5 | 6; X > 4; if (X = 7) then break else 0; X }) then Print("first {Z}")
        break
    # option{}
    loop:
        R := option{ X := 1 | 2 | 3; set V += 100; X > 1; Print("option {X}"); if (X = 2) then break; X }
        Print("not reached")
    Print("option: V={V}")
    # an if in a for's filters: the break leaves the for too
    loop:
        R := for (A := 1..3, B := (if (X := 1 | 2, set V += 1000, X + A = 4, break) then 1 else 0)):
            Print("body {A} {B} V={V}")
            A
        Print("not reached {R.Length}")
    Print("for: V={V}")
