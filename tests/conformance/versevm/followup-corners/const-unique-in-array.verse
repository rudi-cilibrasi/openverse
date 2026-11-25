# followup-corners (#724): The same with the object inside an array,
# All:[]token = array{token{Id := 7}}.
# OpenVerse (Lean and C agreeing): refused, the constant All would hold an
# object with var fields or of a <unique> class, which would be a new one at
# each use: make it a function.
# If Epic refuses it, OpenVerse agrees on the verdict. If it admits it and
# prints id 7 uses same call same, the object in the array is made once:
# OpenVerse would admit it so.
# Not yet compiled or run by UEFN.
token := class<unique>:
    Id:int = 0

All:[]token = array{token{Id := 7}}

Get():[]token = All

Main():void =
    S1 := if (A := All[0], B := All[0], A = B) then "same" else "different"
    S2 := if (A := Get()[0], B := All[0], A = B) then "same" else "different"
    Id := if (A := All[0]) then A.Id else -1
    Print("OVPROBE id {Id} uses {S1} call {S2}")
