# expect: rw, a class below ro, writes its field W at it
entity := class:
    ID:int
player := class(entity):
    Name:string
ro(t:type) := class:
    V:t
rw(t:type) := class(ro(t)):
    var W:t
Main():void =
    X:ro(entity) = rw(player){V := player{ID := 1, Name := "a"}, W := player{ID := 2, Name := "b"}}
