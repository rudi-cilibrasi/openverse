# followup-corners (#724): A module constant of a <unique> class that has a
# field, Shared:token = token{Id := 7}: admitted, and is it the same object
# at every use (two uses compared with =, and one returned by a function)?
# (Epic refused a module constant of a class without specifiers, 3512,
# followup-3582/div-const-constructor, and admitted one of a <computes>
# class.)
# OpenVerse (Lean and C agreeing): refused, the constant Shared would hold
# an object with var fields or of a <unique> class, which would be a new one
# at each use: make it a function.
# If Epic refuses it (3512), OpenVerse agrees on the verdict. If it admits
# it and prints id 7 uses same call same, a module constant is one object
# made once: OpenVerse would admit it and make it once. different anywhere
# would mean the constant is made anew at a use.
# Not yet compiled or run by UEFN.
token := class<unique>:
    Id:int = 0

Shared:token = token{Id := 7}

Get():token = Shared

Main():void =
    A := Shared
    B := Shared
    S1 := if (A = B) then "same" else "different"
    S2 := if (Get() = Shared) then "same" else "different"
    Print("OVPROBE id {Shared.Id} uses {S1} call {S2}")
