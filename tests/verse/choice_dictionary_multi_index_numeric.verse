# set A.Data[0][0] += A.RHS() of ints and rationals: RHS replaces Data first, then the old value is
# read
ca:=class:
    var Data:[][]int=array{array{0,0}}
    RHS()<transacts>:int=block{set Data=array{array{10,20}};7}
cb:=class:
    var Data:[][]rational
    RHS()<transacts>:int=
        if(X:=3/2,Y:=5/2):set Data=array{array{X,Y}}
        7
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    if(Initial:=2/3,Tail:=1/2):
        P:=ca{}
        Q:=cb{Data:=array{array{Initial,Tail}}}
        Rows:=for(A:=(Dup(P)|Dup(Q)),set A.Data[0][0]+=A.RHS()):0
        Print("{Rows.Length}")
        if(P.Data[0][0]=17,P.Data[0][1]=20)then Print("int ok") else Print("bad int")
        if(Q.Data[0][0]=17/2,Q.Data[0][1]=5/2)then Print("ratio ok") else Print("bad ratio")
