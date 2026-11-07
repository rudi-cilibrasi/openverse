# regression test from the #65 review (nest3)
shape := class<abstract>:
    F(O:?v, M:[string]v where v:type):int
square := class(shape):
    F<override>(O:?b, M:[string]b where b:type):int = M.Length
circle := class(shape):
    F<override>(O:?v, M:[string]v where v:type):int = 0
Main():void =
    Ss:[]shape = array{square{}, circle{}}
    for (S : Ss):
        Print("{S.F(false, map{"a" => 1})}")
