# Non-ASCII text: a string's Length counts UTF-8 code units, and the string
# prints back unchanged.
# Tests LANGUAGE.md, Types: "string (= []char)", a char being a UTF-8 code
# unit (Literals: "0oHH char code unit"). A string of code points would give
# lengths 5, 2 and 1, and its index 4 would be the o of hello, not an l.
# OpenVerse prints (Lean and C agree):
#   lengths 6 6 4 | text héllo 日本 😀 | index code units
Main():void =
    A:string = "héllo"
    B:string = "日本"
    C:string = "😀"
    Print("OVPROBE lengths {A.Length} {B.Length} {C.Length}")
    Print("OVPROBE text {A} {B} {C}")
    D := if (A[4] = 'l') then "code units" else if (A[4] = 'o') then "code points" else "other"
    Print("OVPROBE index {D}")
