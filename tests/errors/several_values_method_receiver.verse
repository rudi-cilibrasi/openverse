# expect: 9:45: expected hidden(u), found box(int) (in a call of hidden.Via)
# A method with several values called on a value of a class above its
# own: named as written, hidden.Via, not as its family's function.
box(t:type) := class:
    Count(X:t, Y:[]t)<transacts>:int = Y.Length | Y.Length + 1
hidden(u:type) := class<abstract>(box(u)):
    Via(O:box(string))<transacts>:int = O.Count(("s", array{}))
    Count<override>(X:u, Y:[]u)<transacts>:int
Main()<transacts>:void = for (V := box(int){}.Via(box(string){})) { Print("{V}") }
