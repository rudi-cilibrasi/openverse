# expect: Call calls Run, which has the effect <writes>, which its effects (<computes>) do not allow: remove <computes>
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
cell:=class{var N:int=0}
Run(P:pair(a,b),H:cell,?N:int=block{R:=for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):block{set H.N+=V;V};R.Length} where a:type,b:type):int=N
Call(P:pair(a,b),H:cell where a:type,b:type)<computes>:int=Run(P,H)
Main():void=Print("{Call(dup(int){},cell{})}")
