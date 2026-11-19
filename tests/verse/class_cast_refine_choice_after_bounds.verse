pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){Lo:int=1;Hi:int=2}
Add(X:int,Y:int)<transacts>:int=X+Y
F(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts>:[]tuple(int,b,d,int)=for(I:=Add(dup[P].Lo,dup[Q].Lo)..2,J:=(0|1)){(I,P.A,Q.A,J)}
Main():void=for(V:F(dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"})){Print("{V(0)} {V(1)} {V(2)} {V(3)}")}
