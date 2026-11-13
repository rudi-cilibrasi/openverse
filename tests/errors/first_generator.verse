# expect: 4:10: a generator X : source in first is not supported yet
# The Book's first takes generators as for does; openverse parses them.
Pos(X:int, Xs:[]int)<transacts><decides>:int =
    first(I->Y:Xs; X = Y){I}
Main():void = {}
