# A common ancestor keeps only bounds provided by every alternative (#209).
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
opaque := class { N:int }
root(t:type) := class:
    A:t
    Tag():int = 0
strong(t:subtype(comparable)) := class(root(t)):
    Tag<override>():int = 1
weak(t:type) := class(root(t)):
    Tag<override>():int = 2
Get(P:root(t) where t:type):[]root(t) = for (V:=if (D:=strong[P]) then (D | D) else if (W:=weak[P]) then (W | W) else (P | P)) { V }
Main():void =
    for(R : Get(strong(int){A:=3})) { Print("{R.Tag()}") }
    for(R : Get(weak(string){A:="s"})) { Print("{R.Tag()}") }
    for(R : Get(root(float){A:=1.5})) { Print("{R.Tag()}") }
    for(R : Get(weak(opaque){A:=opaque{N:=1}})) { Print("{R.Tag()}") }
