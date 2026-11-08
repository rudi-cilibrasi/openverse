# a generic class whose type parameter is comparable, with a method that
# could be a value (#218): generic code calling through a function type of
# that method's shape needs no comparable type argument, whether the
# method is used as a value or not
cset(t:subtype(comparable)) := class:
    var Xs:[]t = array{}
    Add(X:t):void = set Xs += array{X}
set_of(t:subtype(comparable)) := class:
    Items:[]t
    Has(X:t):logic = if (Items.Find[X]) then true else false
cell := struct:
    Add:int
Each(Xs:[]u, F:type{_(:u):void} where u:type):void = for (X : Xs) { F(X) }
Map(Xs:[]t, F:type{_(:t):u} where t:type, u:type):[]u = for (X : Xs) { F(X) }
P(X:int):void = Print("p {X}")
Main():void =
    S := cset(int){}
    S.Add(1)
    C := cell{Add := 2}
    Each(array{C.Add}, P)
    Rs := Map(array{1, 2, 3}, set_of(int){Items := array{1, 3}}.Has)
    for (R : Rs) { Print(if (R?) then "yes" else "no") }
    A := S.Add
    A(5)
    Print("{S.Xs.Length}")
    E := subscribable_event(int){}
    Sub := E.Subscribe(P)
    E.Signal(3)
