# expect: (a clause after it, past a generator or a choice, uses D)
# (#243) a for's filter after a refining cast, past a generator, is not its
# branch, which ends at the generator, and has no refinement of its own
# (a generator's source there may use the cast's name; a filter may not)
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    Items:[]t = array{}
    C:int = 1
Use(P:pair(a, b) where a:type, b:type):[]a =
    for (D := dup[P], X : D.Items, D.C > 0) { X }
Main():void = Print("{Use(dup(int){A := 1, B := 2}).Length}")
