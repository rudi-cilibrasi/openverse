# expect: 10:45: this call takes M(int) in the clauses copied for one alternative of a choice and M(string) in those copied for another
# (#283, #106, #335) The clauses after a choice whose alternatives' values are of different types
# are copied for each: a call there of an overloaded method of one class with several values must
# take one of its lists, which is decided before types (a receiver's class picks a hierarchy's).
a := class:
    M(N:int)<transacts>:int = N | N + 1
    M(S:string)<transacts>:int = 7 | 8
Dup(V:t where t:type):t = V | V
Main()<transacts>:void =
    for (X := (Dup(1) | Dup("s")), Y := a{}.M(X)) { Print("y {Y}") }
