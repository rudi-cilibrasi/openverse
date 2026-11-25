# A function named where a function type with an any result is expected is
# converted, as at a void result (#724): every value is an any (the Book's
# tests, Any.versetest:152, and SOL-3799's Apply(F(:t):any, X:t); Epic's
# compiler and Verse VM, UEFN 43.12, followup-refused/named-fn-any-result:
# succ of 0). The function runs, and its result is an any. A method named
# alike.
Succ(X:int):int =
    Print("succ of {X}")
    X + 1

Call(G(:int):any):any = G(0)
Apply(F(:t):any, X:t where t:type):any = F(X)
IntFun(X:int):int = X
StringFun(X:string):string =
    Print(X)
    X
c := class:
    N:int = 3
    Twice(X:int):int =
        Print("twice {X} {N}")
        2 * X
Mk(X:int):c =
    Print("mk {X}")
    c{N := X}

Main():void =
    Call(Succ)
    Apply(IntFun, 1)
    Apply(StringFun, "hello")
    Call(c{}.Twice)
    Call(Mk)
    F:type{_(:int):any} = Succ
    F(5)
    Fs:[]type{_(:int):any} = array{Succ, Mk}
    for (G : Fs). G(9)
