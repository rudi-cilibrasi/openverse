# expect: has the effect <allocates>
# A lifted default retains its class's stricter budget in a transacts caller.
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
cell:=class<allocates><unique>{N:int=0}
Make()<allocates>:cell=cell{}
box:=class<computes>{First:int;Middle:cell=Make();Last:int}
Bad(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:int=box{Last:=dup[Q].C,First:=dup[P].C}.First
Main():void={}
