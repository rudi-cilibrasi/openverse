# Edge of the 3509 rule (#724): F(1, 2) of F(A:[]int, ?B:int = 2), several
# arguments for an array parameter beside a named one. OpenVerse still makes
# the arguments an array, and prints
#   result 4
# If Epic refuses it (3509), an array parameter beside a named one takes no
# several arguments either.
F(A:[]int, ?B:int = 2):int = A.Length + B

Main():void =
    Print("OVPROBE result {F(1, 2)}")
