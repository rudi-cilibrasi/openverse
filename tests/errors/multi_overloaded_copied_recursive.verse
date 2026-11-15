# expect: this call takes the overload Two(int) in the clauses copied for one alternative of a choice and Two(string) in those copied for another
# Recursive overload specialization remains outside the copied-suffix subset.
Dup(V:t where t:type):t = V | V
Two(N:int)<computes>:int = if (N = 0) then 0 else (Two(N - 1) | N)
Two(S:string)<computes>:string = S | S + "!"
Main():void =
    for (A := Dup(1) | Dup("s"), B := Two(A)): Print("{B}")
