# What a data member's definition may do (#724), as UEFN 43.12
# (++Fortnite+Release-43.12-CL-60598086, Verse VM) admits and runs it
# (tests/conformance/versevm/followup-3582): operators, Floor of a rational
# and failure with `or` in a constant (div-const-operator: "half 1"); a call
# in a local constant (div-local-const-call: "limit 3") and in an archetype's
# field value inside a function (div-archetype-call: "size 3"), which are no
# data members; and the converging built-ins the Book's Runtime API
# reference lists (Abs, indexing, Length).
Count():int = 3
thing := class:
    Size:int = 0
Base:int = 6
Half:int = Floor(Base / 4) or 0
Items:[]int = array{4, 5}
First:int = Items[0] or 0
Magnitude:int = Abs(-7) + Items.Length
Main():void =
    Print("half {Half}")
    Limit:int = Count()
    Print("limit {Limit}")
    T := thing{Size := Count()}
    Print("size {T.Size}")
    Print("first {First} magnitude {Magnitude}")
