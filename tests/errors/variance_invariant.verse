# expect: transformer is invariant in t: t is used in Transform's signature (invariant)
entity := class:
    ID:int
player := class(entity):
    Name:string
transformer(t:type) := class:
    Transform(Input:t):t = Input
Main():void =
    PT:transformer(player) = transformer(player){}
    X:transformer(entity) = PT
