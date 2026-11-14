# regression test from the #65 review (ret1): a generic method's
# overrides, its type parameter given by its parameter (the Book's rule,
# ParametricFunctions.versetest 336-378: not by the expected result)
shape := class<abstract>:
    Make(X:u where u:type):[]u
square := class(shape):
    Make<override>(X:u where u:type):[]u = array{}
circle := class(shape):
    Make<override>(X:u where u:type):[]u = array{}
Main():void =
    Ss:[]shape = array{square{}, circle{}}
    for (S : Ss):
        A:[]int = S.Make(1)
        Print("{A.Length}")
