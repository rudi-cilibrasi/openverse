# a generic overload whose later argument is a subtype of an earlier binding (#95 review)
shape := class:
    N:int = 1
sq := class(shape):
    M:int = 2
Q(X:t, Y:t, Z:[]int where t:type):string = "gen"
Q(X:shape, Y:shape, Z:int):string = "nongen"
Main():void =
    Print(Q(shape{}, sq{}, array{}))
    Print(Q(shape{}, sq{}, 1))
