# Overloads on refinements of one base whose intervals have no number in
# common (#724): no value is of both, so they are disjoint domains (the
# Book's tests, WhereConstrainedInts.versetest:179 and
# WhereConstrainedFloats.versetest:59; Epic's compiler and Verse VM, UEFN
# 43.12, followup-refused/refinement-overloads: negative 0 small 1). A call
# takes the overload its argument is of: a literal that meets its conditions,
# or a value of a refinement within it.
small := type{_X:int where 0 <= _X, _X < 65535}
negative := type{_X:int where _X < 0}
digit := type{_X:int where 0 <= _X, _X <= 9}
pos := type{_X:float where _X > -0.0}
neg := type{_X:float where _X < 0.0}

F(X:small):int = X
F(X:negative):int = X + 1
H(X:pos):float = X
H(X:neg):float = X + 1.0
# an int's strict bound is the next one: _X < 0 ends at -1
c := class:
    M(X:small):string = "small"
    M(X:negative):string = "negative"

Main():void =
    Print("negative {F(-1)} small {F(1)}")
    Print("{H(1.0)} {H(-1.0)}")
    S:small = 7
    N:negative = -7
    D:digit = 4
    Print("{F(S)} {F(N)} {F(D)} {F(0)} {F(65534)}")
    Print("{c{}.M(S)} {c{}.M(-3)} {c{}.M(D)}")
    if (T := negative[S - 10]). Print("{F(T)}")
