# expect: 8:43: this call takes the overload Two(int) in the clauses copied for one alternative of a choice and Two(string) in those copied for another
# (#283, #335) The clauses after a choice whose alternatives' values are of different types are
# copied for each: a call there of an overloaded function with several values must take one overload
Two(N:int):int = N | N * 10
Two(S:string):string = S | S + "!"
Dup(V:t where t:type):t = V | V
Main():void =
    for (A := (Dup(1) | Dup("x")), B := Two(A)) { Print("{B}") }
