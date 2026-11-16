box(t:type):=class{A:t}
tight(t:type,u:type):=class(box(t)){E:u;var N:int=1}
Tick(H:tight(t,u),V:t where t:type,u:type)<transacts>:t=
    set H.N+=1
    V|V
Observe(N:int,V:t where t:type)<transacts>:t=
    Print("snapshot {N}")
    V
Run(P0:box(t0),P1:box(t1) where t0:type,t1:type)<transacts>:int=
    R:[]tuple(t0,t1)=for(A0:=if(D:=tight[P0])then Observe(D.N,Tick(D,D.A))else P0.A,A1:=if(D:=tight[P1])then(D.A|D.A)else P1.A):
        (A0,A1)
    R.Length
Main()<transacts>:void=
    H:=tight(int,string){A:=1,E:="s"}
    Print("rows {Run(H,tight(string,int){A:="s",E:=1})}")
    Print("n {H.N}")
