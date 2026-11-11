# Tuple calls preserve instantiated parameter types and call boundaries (#448).
box(t:type) := class:
    Count(X:[]t,O:?t,M:[int]t)<transacts>:int = X.Length+M.Length | (if(V:=O?) then 4 else 9)
hidden(u:type) := class<abstract>(box(u)):
    Count<override>(X:[]u,O:?u,M:[int]u)<transacts>:int
fixed := class(box(int)) {}
Run(P:box(u) where u:type)<transacts>:void = for(V:=P.Count((array{},false,map{}))){Print("{V}")}
Main()<transacts>:void =
    Run(fixed{})
    Run(box(string){})
