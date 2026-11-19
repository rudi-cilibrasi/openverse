# expect: expected b, found a
# An explicitly nested for is a separate producer, unlike a first range's
# own bounds: its refinement cannot escape through its int elements.
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){Hi:int=2}
Bad(P:pair(a,b) where a:type,b:type)<transacts><decides>:b=
    first{I:for(J:=0..dup[P].Hi){J};I>0;P.A}
Main():void=if(V:=Bad[dup(int){A:=1,B:=2}])then Print("{V}")
