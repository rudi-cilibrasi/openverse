# Variance through nested types: arrays, options, tuples and maps are
# covariant, a class's type argument by its own variance, a function type's
# parameter contravariant (a method taking a callback of `t` is covariant in
# `t`), and joins of instances by variance.
entity := class:
    ID:int
player := class(entity):
    Name:string
box(t:type) := class:
    V:t
listener(t:type) := class:
    Value:t
    Each(F:type{_(:t):void}):void = F(Value)
ShowEntity(E:entity):void = Print("each {E.ID}")
Pick(P:logic, A:box(player), B:box(entity)):int =
    J := if (P?) then A else B
    J.V.ID
Main():void =
    Nested:box(box(player)) = box(box(player)){V := box(player){V := player{ID := 1, Name := "n"}}}
    Up:box(box(entity)) = Nested
    Print("nested {Up.V.V.ID}")
    Many:[]box(player) = array{box(player){V := player{ID := 2, Name := "a"}}, box(player){V := player{ID := 3, Name := "b"}}}
    UpMany:[]box(entity) = Many
    Print("array {UpMany[1].V.ID or 0}")
    Opt:?box(player) = option{box(player){V := player{ID := 4, Name := "c"}}}
    UpOpt:?box(entity) = Opt
    if (O := UpOpt?) then Print("option {O.V.ID}")
    L:listener(entity) = listener(player){Value := player{ID := 5, Name := "d"}}
    L.Each(ShowEntity)
    Print("join {Pick(true, box(player){V := player{ID := 6, Name := "e"}}, box(entity){V := entity{ID := 7}})} {Pick(false, box(player){V := player{ID := 8, Name := "f"}}, box(entity){V := entity{ID := 9}})}")
