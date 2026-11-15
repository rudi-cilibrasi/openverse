root(t:type):=class{N:int=1}
pack(a:type,b:type):=class(root(a)){Items:[]int;Value:b;C:int=2}
Run(P:root(a),N:int where a:type)<transacts>:[]int=
    for(D:=pack[P],X:D.Items,Y:=(if(N>0)then(D.C|10)else 0)){Y}
Main():void=
    P:root(int)=pack(int,string){Items:=array{5,6},Value:="hidden"}
    Print("{Run(P,1).Length} {Run(P,0).Length}")
