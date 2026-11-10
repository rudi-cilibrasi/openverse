# expect: 10:28: cannot cast a pair(a, b) to dup(a) here: their type arguments agree only under a refinement, which a cast gives only as the first clause of an if's condition, D := dup[X], whose branch is then typed under it (#209, #243) (and the clauses before it print, change an object or a var, or call a function, which its failure would have to undo: put it first)
# (#243: the Print before the cast would stay when the cast fails, which undoes the whole condition)
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
Bad(P:pair(a, b) where a:type, b:type)<transacts>:int =
    # (the cast comes after a Print)
    if (Print("x"), D := dup[P]) then D.C else 0
Main()<transacts>:void = Print("{Bad(pair(int, int){A := 1, B := 2})}")
