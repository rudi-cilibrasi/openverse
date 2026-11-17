cell:=class{var N:int=0}
Arg(H:cell,N:int)<transacts>:int=
    set H.N+=1
    N
Ow(A:int)<computes>:int=A*5
Ow(S:string)<computes>:int=S.Length|9
Ow(A:int,B:int)<computes>:int=Ow(A)|Ow("{B}")
Values(N:int)<computes><decides>:int=
    N>0
    Ow(N,N)|Values[N-1]
Run(Count:int,Take:int)<transacts>:void=
    H:=cell{}
    for(V:=Values[Arg(H,Count)],V=Take):Print("row {V} {H.N}")
    Print("count {Count} take {Take} state {H.N}")
Main()<transacts>:void=
    Run(0,1)
    Run(2,99)
    Run(2,1)
    Run(2,2)
