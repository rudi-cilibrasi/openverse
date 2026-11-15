pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){Items:[]t;C:int=2;var Counter:int=0}
count:=class{var N:int=0}
Get(P:pair(a,b) where a:type,b:type)<transacts>:pair(a,b)=
    Print("get")
    P
Run(P:pair(a,b),N:int,C:count where a:type,b:type)<transacts>:void=
    for(D:=dup[Get(P)],X:D.Items,Y:=(if(Print("condition {C.N}"),set C.N+=1,N>0)then block{Print("prefix");defer{Print("cleanup {D.C}")};(D.C|10)}else(D.C+20|D.C+30))):
        Print("body {Y} {C.N}")
    Print("after {C.N}")
Main():void=
    D:=dup(int){A:=1,B:=2,Items:=array{5,6}}
    Print("positive")
    Run(D,1,count{})
    Print("negative")
    Run(D,0,count{})
    Print("empty")
    Run(dup(int){A:=1,B:=2,Items:=array{}},1,count{})
    Print("no cast")
    Run(pair(int,int){A:=1,B:=2},1,count{})
