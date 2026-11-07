# regression test from the #65 review (ret1)
shape := class<abstract>:
    Make(X:int where u:type):[]u
square := class(shape):
    Make<override>(X:int where u:type):[]u = array{}
circle := class(shape):
    Make<override>(X:int where u:type):[]u = array{}
Main():void =
    Ss:[]shape = array{square{}, circle{}}
    for (S : Ss):
        A:[]int = S.Make(1)
        Print("{A.Length}")
