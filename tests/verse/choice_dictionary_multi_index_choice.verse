# set A.Data[0][K] += (1|2): the key once, then each alternative, which reads the old value after
# it, as the previous alternative left it
cell:=class{var N:int=0}
Index(H:cell)<transacts>:int=block{Print("key");set H.N+=1;0}
ca:=class{var Data:[][]int=array{array{1}}}
cb:=class{var Data:[][]int=array{array{10}}}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    H:=cell{}
    P:=ca{}
    Q:=cb{}
    Rows:=for(A:=(Dup(P)|Dup(Q)),R:=set A.Data[0][Index(H)]+=(1|2)):R
    Print("{Rows.Length} {H.N}")
    for(V:Rows):Print("{V}")
    if(X:=P.Data[0][0],Y:=Q.Data[0][0]):Print("done {X} {Y}")
