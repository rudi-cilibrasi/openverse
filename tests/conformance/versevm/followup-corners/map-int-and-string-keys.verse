# followup-corners (#724): map{0 => "a", "0" => "b"} with no type written:
# admitted (keys joined to comparable), and what do lookups by 0 and by "0"
# find?
# OpenVerse (Lean and C agreeing): refused, expected int, found string (at
# the second key).
# If Epic refuses it, OpenVerse agrees on the verdict. If it admits it and
# prints length 2 int a string b, a map literal's keys of two types join to
# comparable and an int and a string are different keys: OpenVerse would do
# so.
# Not yet compiled or run by UEFN.
Main():void =
    M := map{0 => "a", "0" => "b"}
    A := if (V := M[0]) then V else "none"
    B := if (V := M["0"]) then V else "none"
    Print("OVPROBE length {M.Length} int {A} string {B}")
