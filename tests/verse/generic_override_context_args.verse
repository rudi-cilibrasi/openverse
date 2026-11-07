# regression test from the #65 review (ctx1)
shape := class<abstract>:
    Cat(A:[]u, X:u where u:type):[]u
square := class(shape):
    Cat<override>(A:[]u, X:u where u:type):[]u = A + array{X}
circle := class(shape):
    Cat<override>(A:[]v, X:v where v:type):[]v = array{X} + A
Main():void =
    Ss:[]shape = array{square{}, circle{}}
    for (S : Ss):
        B := S.Cat(array{}, 3)
        Print("{B.Length}")
        C := S.Cat(array{1,2}, 3)
        Print("{C.Length}")
