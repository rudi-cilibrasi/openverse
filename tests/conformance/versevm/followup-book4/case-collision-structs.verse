# Asks whether two structs of one scope whose names differ only in case
# collide, as two classes do (UEFN 43.12 refuses cc and CC, 9002 "Found
# existing type 'CC'", followup-book3/case-collision-classes). OpenVerse
# takes every type alike and refuses it ("the types ss and SS have names
# that differ only in case", #724). If Epic admits it, it prints
#   lower 1 | upper 2
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 9002 (L9) "Found existing type 'SS' that
# is already being created this compile. Please rename the struct to be case
# insen".
ss := struct:
    V:int = 1

SS := struct:
    V:int = 2

Main():void =
    Print("OVPROBE lower {ss{}.V}")
    Print("OVPROBE upper {SS{}.V}")
