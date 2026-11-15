Dup(V:t where t:type):t = V | V
Pick(N:int):int = N | N + 1
Pick(S:string):int = 7 | 8
Main()<transacts>:void =
    var Before:int = 0
    for (block{set Before += 1; true?}, A := Dup(1) | Dup("s"), B := Pick(A), B < 8):
        Print("{B} {Before}")
    Print("end {Before}")
