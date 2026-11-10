# Interfaces referred to through views (#351): a variable's initial object
# of a class whose pins relate its type arguments (both is abstract, so a
# class below is the only one there is): dup gives both its argument
# twice, pr a compound of it, wrap two compounds; in generic code too
container(t:type) := interface:
    Get():t
sink(u:type) := interface:
    Put(X:u):int
both(t:type, u:type) := class<abstract>(container(t), sink(u)):
    V:t
    Get<override>():t = V
dup(t:type) := class(both(t, t)):
    Put<override>(X:t):int = 10
pr(t:type) := class(both(t, []t)):
    Put<override>(X:[]t):int = X.Length
wrap(t:type) := class(both([]t, ?t)):
    Put<override>(X:?t):int = if (Y := X?) then 1 else 2
MkW(V:x where x:type):sink(?x) = wrap(x){V := array{V}}
Main():void =
    S:sink(int) = dup(int){V := 1}
    P:sink([]int) = pr(int){V := 1}
    W:sink(?int) = wrap(int){V := array{1}}
    M := MkW("m")
    Print("{S.Put(2)} {P.Put(array{1, 2})} {W.Put(false)} {W.Put(option{3})} {M.Put(option{"n"})}")
