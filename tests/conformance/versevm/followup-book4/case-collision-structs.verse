# Asks whether two structs of one scope whose names differ only in case
# collide, as two classes do (UEFN 43.12 refuses cc and CC, 9002 "Found
# existing type 'CC'", followup-book3/case-collision-classes). OpenVerse
# takes every type alike and refuses it ("the types ss and SS have names
# that differ only in case", #724). If Epic admits it, it prints
#   lower 1 | upper 2
ss := struct:
    V:int = 1

SS := struct:
    V:int = 2

Main():void =
    Print("OVPROBE lower {ss{}.V}")
    Print("OVPROBE upper {SS{}.V}")
