# logic as a parameter, result and field type (issue #8): `logic` is both a
# keyword, for logic{…}, and a type name.
flags := struct:
    Ready:logic = false
    Seen:[]logic = array{}

Flip(B:logic):logic = if (B?) then false else true

Count(Bs:[]logic):int =
    var N:int = 0
    for (B : Bs, B?) { set N += 1 }
    N

Main():void =
    F := flags{Ready := Flip(false), Seen := array{true, false, true}}
    if (F.Ready?) then Print("ready")
    Print("{Count(F.Seen)} seen")
    O:?logic = option{logic{1 > 2}}
    if (V := O?, not V?) then Print("an option of false")
