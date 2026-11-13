# The right operand of = and <> is checked at the left's type, else its own
# type is inferred: an empty literal of another type than the left's ("" after
# (), a void, false, a logic or an option) goes through a temporary of its
# type. All of them are the one empty value (Book of Verse ch. 2), so they are
# equal, whatever their types.
Same(V:void, O:?int, L:logic)<decides>:void = { V = ""; () = ""; O = ""; L = ""; false = "" }
Differ(V:void, O:?int, L:logic)<decides>:void = { V <> ""; () <> ""; O <> ""; L <> ""; false <> "" }
Main():void =
    if (Same[(), false, false]) then Print("same") else Print("not same")
    if (Differ[(), false, false]) then Print("differ") else Print("not differ")
    X:void = 1
    if (X = "") then Print("void eq") else Print("void ne")
    if (() <> "", () = ()) then Print("unit ne")
    # (the other way round, as before: "" is checked at the right's type)
    if ("" = ()) then Print("rev eq") else Print("rev ne")
