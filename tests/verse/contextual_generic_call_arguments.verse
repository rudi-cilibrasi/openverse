# Generic calls needing an expected type can occur inside another argument.
Empty(?Default:?t=false where t:type):?t=Default
Id(X:t where t:type):t=X
Choose(M:[?int]t,Other:t where t:type):t=Other
PairCall(Values:tuple(?t,t),Other:t where t:type):t=Other
ArrayCall(Values:[]?t,Other:t where t:type):t=Other
OptionCall(Value:?t,Other:t where t:type):t=Other
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){Index:int=0}
Leaf(X:t,?Index:int=0 where t:type):t=X
Refined(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<decides>:b=
    Choose(map{Empty()=>Leaf(P.A,?Index:=dup[Q].Index)},dup[P].B)
Main():void=
    Print("plain {Choose(map{Empty()=>7},9)}")
    Print("wrapped {Choose(map{Id(Empty())=>7},9)}")
    Print("pair {PairCall((Empty(),7),9)}")
    Print("array {ArrayCall(array{Empty()},9)}")
    Print("option {OptionCall(Empty(),9)}")
    if(V:=Refined[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"}])then Print("refined {V}")else Print("wrong")
