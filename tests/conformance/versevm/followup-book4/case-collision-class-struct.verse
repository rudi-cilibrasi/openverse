# Asks the same of a class cc and a struct CC. OpenVerse refuses it (#724).
# If Epic admits it, it prints
#   lower 1 | upper 2
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 9002 (L6) "Found existing type 'CC' that
# is already being created this compile. Please rename the struct to be case
# insen".
cc := class:
    V:int = 1

CC := struct:
    V:int = 2

Main():void =
    Print("OVPROBE lower {cc{}.V}")
    Print("OVPROBE upper {CC{}.V}")
