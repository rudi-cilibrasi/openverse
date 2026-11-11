# Tuple calls preserve instantiated parameter types and call boundaries (#448).
box(t:type) := class:
    Count(X:t,Y:[]t)<transacts>:int = Y.Length | Y.Length+1
    Via(O:box(string))<transacts>:int = O.Count(("s",array{}))
hidden(u:type) := class<abstract>(box(u)):
    Count<override>(X:u,Y:[]u)<transacts>:int
Main()<transacts>:void = for(V:=box(int){}.Via(box(string){})){Print("{V}")}
