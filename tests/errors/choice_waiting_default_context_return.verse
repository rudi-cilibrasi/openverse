# expect: return is not allowed in a parameter
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
cell:=class{var N:int=0}
Run(P:pair(a,b),H:cell,?N:int=block{R:=for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):block{Sleep(0.1);return V;V};R.Length} where a:type,b:type)<suspends>:int=N
Use(P:pair(a,b),H:cell where a:type,b:type)<suspends>:int=Run(P,H)
Main()<suspends>:void=Print("{Use(dup(int){},cell{})}")
