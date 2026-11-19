# Edge of the 3509 rule (#724): F(1, 2) of F(A:[]int, ?B:int = 2), several
# arguments for an array parameter beside a named one. OpenVerse still makes
# the arguments an array, and prints
#   result 4
# If Epic refuses it (3509), an array parameter beside a named one takes no
# several arguments either.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3509 (L9) "This function parameter
# expects a value of type tuple([]int,?B:int = ...), but this argument is an
# incompatible value of".
F(A:[]int, ?B:int = 2):int = A.Length + B

Main():void =
    Print("OVPROBE result {F(1, 2)}")
