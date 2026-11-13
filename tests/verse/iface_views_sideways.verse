# (#351) a cast of a reference through views to an interface beside it: a
# test of each class below both (c, whose view gives i1 int)
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
