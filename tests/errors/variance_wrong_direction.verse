# expect: so producer(entity) is a producer(player) only when entity is a player
entity := class:
    ID:int
player := class(entity):
    Name:string
producer(t:type) := class:
    Value:t
Main():void =
    P:producer(entity) = producer(entity){Value := entity{ID := 1}}
    Q:producer(player) = P
