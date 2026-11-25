# followup-corners (#724): A <computes> function that returns a module
# constant of a class<unique><allocates>: is the constant admitted (the
# class's construction effect written as <allocates>, not the default
# <transacts>), and may a <computes> function read it?
# OpenVerse (Lean and C agreeing): refused, the constant Shared would hold
# an object with var fields or of a <unique> class, which would be a new one
# at each use: make it a function (before any question of the function's
# effect).
# If Epic refuses it, the diagnostic says which: the constant (3512: an
# <allocates> construction is no data member's) or the function (reading it
# is not <computes>). If it admits it and prints id 7 call same, OpenVerse
# would admit both.
# Not yet compiled or run by UEFN.
token := class<unique><allocates>:
    Id:int = 0

Shared:token = token{Id := 7}

Get()<computes>:token = Shared

Main():void =
    S := if (Get() = Shared) then "same" else "different"
    Print("OVPROBE id {Get().Id} call {S}")
