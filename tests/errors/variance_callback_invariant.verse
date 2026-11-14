# expect: apply is invariant in t: t is used in V (covariant), Apply's signature (invariant)
entity := class:
    ID:int
player := class(entity):
    Name:string
apply(t:type) := class:
    V:t
    Apply(F:type{_(:t):t}):t = F(V)
Main():void =
    A:apply(entity) = apply(player){V := player{ID := 1, Name := "p"}}
