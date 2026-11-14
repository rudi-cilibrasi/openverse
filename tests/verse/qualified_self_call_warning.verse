# (q:)F(…) of Self in an override of F calls F on Self, which dispatches to
# the override again: the warnings of the Book of Verse's tests (SOL-3564),
# 2003 where (super:)F(…) reaches q's implementation, 2004 where q is
# further up. Another overload, a method that overrides nothing and
# (super:) warn of nothing. The warned calls are never run here.
a := class:
    F(N:int):int = N + 1
    G():string = "a"
    G(N:int):string = "a{N}"
b := class(a):
    F<override>(N:int):int = if (N > 100) then (a:)F(N) else (super:)F(N) + 10
    G<override>():string = (a:)G(2)
c := class(b):
    F<override>(N:int):int = if (N > 100) then (a:)F(N) else (super:)F(N) + 100
i := interface:
    H():string
d := class<abstract>(i) {}
e := class(d):
    H<override>():string = if (false?) then (i:)H() else "e"
Main():void =
    Print("{b{}.F(1)} {c{}.F(1)} {b{}.G()} {e{}.H()}")
