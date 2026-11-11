# expect: Call constructs box, whose block: (in box), which has the effect <writes>, which its effects (<computes>) do not allow: remove <computes>
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
box(a:type,b:type):=class:
    P:pair(a,b)
    var N:int=0
    block:set N=block{R:=for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):V;R.Length}
Call(P:pair(a,b) where a:type,b:type)<computes>:int=box(a,b){P:=P}.N
Main():void=Print("{Call(dup(int){})}")
