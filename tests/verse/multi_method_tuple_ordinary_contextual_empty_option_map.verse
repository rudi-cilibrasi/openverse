# Tuple calls preserve instantiated parameter types and call boundaries (#448).
box(t:type) := class:
    Count(X:[]t,O:?t,M:[int]t)<transacts>:int = X.Length+M.Length | (if(V:=O?) then 4 else 9)
hidden(u:type) := class<abstract>(box(u)):
    Count<override>(X:[]u,O:?u,M:[int]u)<transacts>:int
fixed := class(box(int)) {}
# (box only takes u in, so a box(u) gives no u, the Book's rule,
# ParametricFunctions.versetest 356: the type is given as an argument)
Run(u:type, P:box(u))<transacts>:void = for(V:=P.Count((array{},false,map{}))){Print("{V}")}
Main()<transacts>:void =
    Run(int, fixed{})
    Run(string, box(string){})
