# Slices of a string with one and two indices, at and past the edges.
# Tests LANGUAGE.md, Array methods: "A.Slice[i, j], A.Slice[i]" (all
# failable); Epic's digest: Slice[i, j] "Fails unless 0 <= StartIndex <=
# StopIndex <= Input.Length", Slice[i] "Succeeds if 0 <= StartIndex <=
# Input.Length". Brackets mark each result so an empty one shows.
# OpenVerse prints (Lean and C agree):
#   ok [el] [llo] [hello] [] [] | bad fails fails fails fails
Main():void =
    S:string = "hello"
    if (A := S.Slice[1, 3], B := S.Slice[2], C := S.Slice[0, 5], D := S.Slice[5], E := S.Slice[2, 2]):
        Print("OVPROBE ok [{A}] [{B}] [{C}] [{D}] [{E}]")
    F := if (S.Slice[3, 2]) then "ok" else "fails"
    G := if (S.Slice[6]) then "ok" else "fails"
    H := if (S.Slice[0, 6]) then "ok" else "fails"
    I := if (S.Slice[-1, 2]) then "ok" else "fails"
    Print("OVPROBE bad {F} {G} {H} {I}")
