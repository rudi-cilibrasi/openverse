pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){Lo:int=1}
cell:=class{var Init:int=0;var Sum:int=0}
Add(X:int,Y:int)<transacts>:int=X+Y
Initialize(H:cell)<transacts>:int={set H.Init+=1;Print("init {H.Init}");0}
F0(P:pair(a,b),Q:pair(c,d),H:cell,Limit:int where a:type,b:type,c:type,d:type)<transacts><decides>:[]tuple(int,b,d,int)=
    for(var Count:int=Initialize(H),I:=Add(dup[P].Lo,dup[Q].Lo)..2,J:=(0|1),Written:=block{set Count+=1;set H.Sum+=Count;Print("step {Count}");1},J>Limit):
        Print("body {J}")
        (I,P.A,Q.A,Count)
F1(P:pair(a,b),Q:pair(c,d),H:cell,Limit:int where a:type,b:type,c:type,d:type)<transacts><decides>:[]tuple(int,b,d,int)=
    for(I:=Add(dup[P].Lo,dup[Q].Lo)..2,var Count:int=Initialize(H),J:=(0|1),Written:=block{set Count+=1;set H.Sum+=Count;Print("step {Count}");1},J>Limit):
        Print("body {J}")
        (I,P.A,Q.A,Count)
F2(P:pair(a,b),Q:pair(c,d),H:cell,Limit:int where a:type,b:type,c:type,d:type)<transacts><decides>:[]tuple(int,b,d,int)=
    for(I:=Add(dup[P].Lo,dup[Q].Lo)..2,J:=(0|1),var Count:int=Initialize(H),Written:=block{set Count+=1;set H.Sum+=Count;Print("step {Count}");1},J>Limit):
        Print("body {J}")
        (I,P.A,Q.A,Count)
Run0(Label:string,Limit:int)<transacts>:void=
    H:=cell{}
    Print(Label)
    if(Rows:=F0[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"},H,Limit])then block:
        Print("rows {Rows.Length}")
        for(V:Rows){Print("{V(0)} {V(1)} {V(2)} {V(3)}")}
    else Print("failure")
    Print("state {H.Init} {H.Sum}")
Run1(Label:string,Limit:int)<transacts>:void=
    H:=cell{}
    Print(Label)
    if(Rows:=F1[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"},H,Limit])then block:
        Print("rows {Rows.Length}")
        for(V:Rows){Print("{V(0)} {V(1)} {V(2)} {V(3)}")}
    else Print("failure")
    Print("state {H.Init} {H.Sum}")
Run2(Label:string,Limit:int)<transacts>:void=
    H:=cell{}
    Print(Label)
    if(Rows:=F2[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"},H,Limit])then block:
        Print("rows {Rows.Length}")
        for(V:Rows){Print("{V(0)} {V(1)} {V(2)} {V(3)}")}
    else Print("failure")
    Print("state {H.Init} {H.Sum}")
Main()<transacts>:void=
    Run0("0-all",-1)
    Run0("0-second",0)
    Run0("0-none",1)
    Run1("1-all",-1)
    Run1("1-second",0)
    Run1("1-none",1)
    Run2("2-all",-1)
    Run2("2-second",0)
    Run2("2-none",1)
