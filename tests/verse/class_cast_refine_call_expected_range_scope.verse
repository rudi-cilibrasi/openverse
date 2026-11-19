# Range producers replay their bound refinements in the body; arithmetic
# temporaries and copied-overload alternatives must not erase either proof.
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){Lo:int=1;Hi:int=2}
Add(X:int,Y:int):int=X+Y
Dup(V:t where t:type):t=V|V
Mix(N:int)<transacts>:int=N|N+1
Mix(S:string)<transacts>:int=7
Math(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts>:[]tuple(int,b,d)=
    for(I:=dup[P].Lo+0..dup[Q].Hi+0){(I,P.A,Q.A)}
Bare(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts>:[]tuple(int,b,d)=
    for(I:=dup[P].Lo..dup[Q].Hi){(I,P.A,Q.A)}
Copied(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts>:[]tuple(int,b,d,int)=
    for(I:=dup[P].Lo+0..dup[Q].Hi+0,A:=Dup(1)|Dup("s"),N:=Mix(A)){(I,P.A,Q.A,N)}
Main():void=
    P:=dup(int){A:=7,B:=9}
    Q:=dup(string){A:="left",B:="right"}
    for(V:Math(P,Q)){Print("math {V(0)} {V(1)} {V(2)}")}
    for(V:Bare(P,Q)){Print("bare {V(0)} {V(1)} {V(2)}")}
    for(V:Copied(P,Q)){Print("copied {V(0)} {V(1)} {V(2)} {V(3)}")}
