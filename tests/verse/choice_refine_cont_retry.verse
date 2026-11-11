# A failed suffix retries the outer refined choice.
pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
Use(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type):void =
    if(W:=if(D:=dup[P])then(D.C|D.C+1)else 0,Z:=if(E:=dup[Q])then(E.C|E.C+1)else 0,W=5,Z=4)then Print("win {W}")else Print("none")
Main():void = Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})
