# A string's Length and its indexing: chars in range, failure out of range.
# Tests LANGUAGE.md, Types: "string (= []char)"; Maps/arrays: indexing fails
# out of range. A char interpolates as itself (ToString(Character:char)).
# OpenVerse prints (Lean and C agree):
#   chars hoe length 5 | out fails fails fails empty length 0
Main():void =
    S:string = "hello"
    if (A := S[0], B := S[4], C := S[1]):
        Print("OVPROBE chars {A}{B}{C} length {S.Length}")
    X := if (S[5]) then "ok" else "fails"
    Y := if (S[-1]) then "ok" else "fails"
    E:string = ""
    W := if (E[0]) then "ok" else "fails"
    Print("OVPROBE out {X} {Y} {W} empty length {E.Length}")
