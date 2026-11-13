# (#351, #53) a cast from named (referred to through views, as it is above
# i2) to i2(t), whose t it opens: a test of each class below both (c, whose
# view gives i2 string)
named := interface:
    Name():string
i1(t:type) := interface(named):
    A():t
i2(t:type) := interface(named):
    B():t
c := class(i1(int), i2(string)):
    A<override>():int = 7
    B<override>():string = "seven"
    Name<override>():string = "c"
Main():void =
    N:named = c{}
    if (I := i2[N]) then Print("i2") else Print("not i2")
