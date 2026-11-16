box:=class<computes>{Count:int}
pair(a:type,b:type):=class<computes>{A:a;B:b}
dup(t:type):=class<computes>(pair(t,t)){Lo:int=1}
Add(X:int,Y:int)<computes>:int=X+Y
F(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<computes>:[]tuple(int,b,d,int)=
    for(var Count:int=0,I:=Add(dup[P].Lo,dup[Q].Lo)..2,J:=(0|1)):
        set Count+=1
        B:=box{Count:=Count}
        (I,P.A,Q.A,B.Count)
Main():void=
    for(V:F(dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"})):
        Print("{V(0)} {V(1)} {V(2)} {V(3)}")
