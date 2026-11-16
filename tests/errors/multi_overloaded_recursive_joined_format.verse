# expect: no ToString for comparable
# The condition's heterogeneous result has a joined type in the branch.
Values(N:int)<computes>:int=if(N=0)then 0 else(Values(N-1)|N)
Values(S:string)<computes>:string=S|S+"!"

Dup(V:t where t:type):t=V|V
Accept(N:int)<computes><decides>:void=N>0
Accept(S:string)<computes><decides>:void=S.Length>1
Main()<transacts>:void=
    if(A:=Dup(1)|Dup("s"),V:=Values(A),Accept[V]):Print("first<{V}>")
