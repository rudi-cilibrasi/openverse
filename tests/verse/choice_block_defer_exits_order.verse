# The cleanup a break or return runs as it leaves blocks with choices of their own
# (#283), in the order of any scope's: last registered first, only those reached,
# the innermost scope first, a return's value before them all, then the loop's and
# the function's. A defer: reads what the clauses set; a value whose clauses fail
# runs none, since what they did is rolled back.
Value(N:int):int =
    Print("value {N}")
    N
Leave(I:int)<transacts>:int =
    defer: Print("function")
    var V:int = 0
    loop:
        defer: Print("loop V={V}")
        if (I = 0, X := block{ defer: Print("a"); defer: Print("b"); Y := 1 | 2; if (Y = 2) then break; Y }, X > 5) then Print("not reached")
        if (I = 1, X := block{ defer: Print("a"); Y := 1 | 2; if (Y = 1) then break; defer: Print("b"); Y }, X > 5) then Print("not reached")
        if (I = 2, X := block{ defer: Print("a"); Y := 1 | 2; set V = Y * 10; defer: Print("b V={V}"); if (Y = 2) then break; Y }, X > 5) then Print("not reached")
        if (I = 3, X := block{ defer: Print("outer"); Y := 1 | 2; Z := block{ defer: Print("inner"); W := 3 | 4; if (W = 4, Y = 2) then return Value(W + Y); W }; Z + Y }, X > 50) then Print("not reached")
        if (I = 4, X := block{ defer: Print("outer"); Y := 1 | 2; if (Y = 2) { defer: Print("inner"); return Value(Y) }; Y }, X > 5) then Print("not reached")
        if (I = 5, X := block{ defer: Print("d V={V}"); Y := 1 | 2 | 3; set V = Y; Y > 5 }) then Print("not reached")
        Print("no exit V={V}")
        break
    V
Main()<transacts>:void =
    for (I := 0..5):
        Print("left {I}: {Leave(I)}")
