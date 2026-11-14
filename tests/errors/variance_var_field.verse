# expect: cell is invariant in t: t is used in var V (invariant)
entity := class:
    ID:int
player := class(entity):
    Name:string
cell(t:type) := class:
    var V:t
Main():void =
    C:cell(player) = cell(player){V := player{ID := 1, Name := "a"}}
    D:cell(entity) = C
    set D.V = entity{ID := 2}
