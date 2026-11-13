# expect: no ToString for t'
# (#351) a cast to an interface beside the object's that no interface above
# both relates to it: its type argument is opened, whatever the classes
# below both give it (c gives both int), so J.A() is no int
i1(t:type) := interface:
    A():t
i2(t:type) := interface:
    B():t
c(t:type) := class(i1(t), i2(t)):
    V:t
    A<override>():t = V
    B<override>():t = V
Main():void =
    I:i2(int) = c(int){V := 7}
    if (J := i1[I]) then Print("i1 {J.A()}") else Print("not i1")
