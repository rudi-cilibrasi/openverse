# In first{…} a comma joins the clauses around it into a tuple ("Comma is not the same as
# semicolon", the Book of Verse's tests, FlowControl/first.versetest:204-208): the value is the
# tuple of the clauses' values at the first iteration where all of them succeed. A generator's
# and a definition's value is its name's; a comparison's is its left operand.
Main():void =
    if (12 = first{X:=1..5; 3*X>10}) then Print("semicolons: the last clause's value, 12")
    if ((4, 12) = first{X:=1..5, 3*X>10}) then Print("commas: the tuple (4, 12)")
    if (T := first{X:array{7, 8, 9}, X > 7, Y := X * 2}) then Print("{T(0)} {T(1)} {T(2)}")
    if (T := first{X:=1..3, Y:=1..X, X + Y > 4}) then Print("{T(0)} {T(1)} {T(2)}")
    if (T := first{X:=1..5, 3*X>100}) then Print("no") else Print("no iteration succeeds")
