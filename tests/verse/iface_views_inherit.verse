# Interfaces referred to through views (#351), at classes that only
# inherit: both's methods are the interfaces' defaults, at a variable of
# container, which gives it fewer type arguments than it has; low and mid
# give both compounds of their own and override nothing, so their calls are
# typed at both's places, not through pins they do not have
container(t:type) := interface:
    Get(X:t):t = X
sink(u:type) := interface:
    Put(X:u):string = "sink"
both(t:type, u:type) := class(container(t), sink(u)):
    V:t
bothO(t:type, u:type) := class(container(t), sink(u)):
    V:t
    Put<override>(X:u):string = "bothO"
low(t:type, u:type) := class(bothO(t, []u)):
    W:u
mid(t:type, w:type) := class(bothO(t, ?w)):
    W:w
lowest(a:type) := class(mid([]a, a)):
    Put<override>(X:?a):string = "lowest"
GC(Cs:[]container(x), V:x where x:type):x =
    var R:x = V
    for (C : Cs) { set R = C.Get(V) }
    R
GP(S:sink(x), V:x where x:type):string = S.Put(V)
Main():void =
    C:container(int) = both(int, string){V := 1}
    Print("{C.Get(5)} {GC(array{both(int, string){V := 1}}, 6)}")
    S:sink([]int) = low(int, int){V := 1, W := 2}
    Print("{S.Put(array{3})} {GP(S, array{4})}")
    Ss:[]sink(?int) = array{bothO(char, ?int){V := 'c'}, mid(char, int){V := 'd', W := 1}, lowest(int){V := array{}, W := 1}}
    for (X : Ss) { Print("{X.Put(false)} {GP(X, option{1})}") }
