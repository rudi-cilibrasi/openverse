# expect: (a clause after it, past a generator or a choice, uses D)
# (#243) a for's clauses after a refining cast, past a generator, are not
# its branch, which ends at the generator: they cannot use its name
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    Items:[]t = array{}
Use(P:pair(a, b) where a:type, b:type):[]a =
    for (D := dup[P], X : D.Items) { X }
Main():void = Print("{Use(dup(int){A := 1, B := 2}).Length}")
