# expect: so consumer(player) is a consumer(entity) only when entity is a player
entity := class:
    ID:int
player := class(entity):
    Name:string
consumer(t:type) := class:
    Take(X:t):void = {}
Main():void =
    C:consumer(player) = consumer(player){}
    D:consumer(entity) = C
