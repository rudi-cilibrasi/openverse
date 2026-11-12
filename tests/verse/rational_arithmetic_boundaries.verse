Check(Tag:string,R:rational,N:int,D:int):void=
    if(E:=N/D,R=E)then Print("{Tag} {Floor(R)} {Ceil(R)}")else Print("bad {Tag}")
Main():void=
    K:=9223372036854775807
    M:=-9223372036854775807-1
    V:rational=M
    if(A:=1/K,B:=(K-1)/K,C:=K/(K-1),D:=M/(K-1),E:=K/2,F:=2/K,G:=M/K):
        Check("sum",A+B,1,1)
        Check("cancel",C+D,-1,K-1)
        Check("product",E*F,1,1)
        Check("wide-sum",G+B,-2,K)
        Check("wide-zero",G-G,0,1)
        Check("min",V-0,M,1)
        Check("zero",V-V,0,1)
        if(R:=V/V)then Check("divide",R,1,1)else Print("bad")
