# expect: no overload of Pick takes (string)
# Copy-specific picks still require every alternative's call to fit one overload.
Dup(V:t where t:type):t = V | V
Pick(N:int):int = N | N + 1
Pick(B:logic):int = 7 | 8
Main():void =
    for (A := Dup(1) | Dup("x"), B := Pick(A)): Print("{B}")
