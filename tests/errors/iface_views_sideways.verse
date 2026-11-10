# expect: to i1, which is neither above nor below i2, is not supported yet (#351)
# a cast of a reference through views to an interface beside it, whose
# type arguments no class's view gives
i1(t:type) := interface:
    A():t
i2(t:type) := interface:
    B():t
c := class(i1(int), i2(string)):
    A<override>():int = 7
    B<override>():string = "seven"
Main():void =
    I:i2(string) = c{}
    if (J := i1[I]) then Print("i1") else Print("not i1")
