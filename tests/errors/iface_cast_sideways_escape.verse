# expect: cannot cast an i2(int) to i1 here: the cast opens i1's type argument t for the code after it, outside which its value, an i1(t'), would name what is unknown (#250)
# (#351, #250) the value of option{} of a cast beside the object's type,
# whose type argument it opens, would name it outside
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
    X := option{i1[I]}
    if (X?) then Print("i1")
