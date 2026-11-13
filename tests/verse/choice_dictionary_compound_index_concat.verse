# set A.Data[0] += A.More(): More replaces Data first, so the old value is the new Data's element
ca:=class:
    var Data:[][]int=array{array{1},array{2}}
    More()<transacts>:[]int=block{set Data=array{array{10},array{20}};array{3}}
cb:=class:
    var Data:[][]string=array{array{"a"},array{"b"}}
    More()<transacts>:[]string=block{set Data=array{array{"x"},array{"y"}};array{"c"}}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    P:=ca{}
    Q:=cb{}
    Rows:=for(A:=(Dup(P)|Dup(Q)),set A.Data[0]+=A.More()):0
    Print("{Rows.Length}")
    if(P.Data[0].Length=2,P.Data[0][0]=10,P.Data[0][1]=3,P.Data[1][0]=20)then Print("ints ok") else Print("bad ints")
    if(Q.Data[0].Length=2,Q.Data[0][0]="x",Q.Data[0][1]="c",Q.Data[1][0]="y")then Print("strings ok") else Print("bad strings")
