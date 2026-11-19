pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){Lo:int=1}
box:=class{Count:int}
Add(X:int,Y:int)<transacts>:int=X+Y
F0(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:[]tuple(int,b,d,int)=
    for(var Count:int=0,I:=Add(dup[P].Lo,dup[Q].Lo)..2,J:=(0|1),Written:=block{set Count+=1;1}):
        B:=box{Count:=Count}
        (I,P.A,Q.A,B.Count)
F1(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:[]tuple(int,b,d,int)=
    for(I:=Add(dup[P].Lo,dup[Q].Lo)..2,var Count:int=0,J:=(0|1),Written:=block{set Count+=1;1}):
        B:=box{Count:=Count}
        (I,P.A,Q.A,B.Count)
F2(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:[]tuple(int,b,d,int)=
    for(I:=Add(dup[P].Lo,dup[Q].Lo)..2,J:=(0|1),var Count:int=0,Written:=block{set Count+=1;1}):
        B:=box{Count:=Count}
        (I,P.A,Q.A,B.Count)
Main():void=
    Print("before-bound")
    for(V:F0[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"}]):
        Print("{V(0)} {V(1)} {V(2)} {V(3)}")
    Print("after-bound")
    for(V:F1[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"}]):
        Print("{V(0)} {V(1)} {V(2)} {V(3)}")
    Print("after-choice")
    for(V:F2[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"}]):
        Print("{V(0)} {V(1)} {V(2)} {V(3)}")
