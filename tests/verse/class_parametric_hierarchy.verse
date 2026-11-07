# Parametric classes in hierarchies (#39). A subclass passes its type
# parameters to its parent (in any order), or fixes the parent's type
# arguments; it cannot add type parameters of its own yet.

shape(t:type) := class<abstract>:
    Label:t
    Area():int
    Describe():string = "shape"

square(t:type) := class(shape(t)):
    Side:int
    Area<override>():int = Side * Side

rect(t:type) := class(shape(t)):
    var W:int
    H:int
    Area<override>():int = W * H
    Describe<override>():string = "rect"

# a subclass that fixes the type argument (it cannot override: code generic
# over shape(t) could not call its implementation)
cell(t:type) := class:
    var Value:t
    Get():t = Value
intcell := class(cell(int)):
    Bump():void = set Value += 1

Total(Ss:[]shape(t) where t:type):int =
    var N:int = 0
    for (S : Ss) { set N += S.Area() }
    N

Widen(R:rect(t) where t:type):void = set R.W += 1

# a subclass that swaps its parent's type parameters
pair(x:type, y:type) := class:
    First:x
    Second:y
swap(a:type, b:type) := class(pair(b, a)):
    Mine:a
    Flip():pair(a, b) = pair(a, b){First := Mine, Second := First}

Kind(S:shape(string)):string =
    if (Q := square[S]) then "square of side {Q.Side}"
    else if (R := rect[S]) then "rect {R.W} by {R.H}"
    else "something else"

Main():void =
    Ss:[]shape(string) = array{
        square(string){Label := "a", Side := 2},
        rect(string){Label := "b", W := 2, H := 3}}
    for (S : Ss) { Print("{S.Label}: {S.Area()} {S.Describe()}, {Kind(S)}") }
    Print("total {Total(Ss)}")
    # the same rect, through the array and through R
    if (R := rect[Ss[1]]):
        Widen(R)
        Print("total after widening {Total(Ss)}")
    Ns:[]shape(int) = array{square(int){Label := 1, Side := 3}}
    Print("total {Total(Ns)}")
    # a join of two subclasses at the same type argument
    X := if (Ss.Length > 1) then square(int){Label := 7, Side := 3} else rect(int){Label := 8, W := 1, H := 1}
    Print("{X.Label} {X.Area()}")
    W := swap(int, string){First := "s", Second := 2, Mine := 9}
    P:pair(string, int) = W
    Print("{P.First} {P.Second}")
    F := W.Flip()
    Print("{F.First} {F.Second}")
    if (W2 := swap[P]) then Print("a swap with {W2.Mine}")
    I := intcell{Value := 4}
    I.Bump()
    C:cell(int) = I
    Print("{C.Get()}")
    if (I2 := intcell[C]) then Print("an intcell")
