pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){}
holder:=class{var N:int=0}
Touch(H:holder,Reject:int)<transacts><decides>:int=
    set H.N+=1
    Print("touch {H.N}")
    H.N<>Reject
    H.N
Rows(P:pair(a,b),H:holder,Reject:int where a:type,b:type)<transacts><decides>:int=
    R:=for(V:=if(D:=dup[P])then(D.A|D.B)else P.B) do Touch[H,Reject]
    R.Length
Main()<transacts>:void=
    P:=dup(int){A:=1,B:=2}
    H:=holder{}
    if(N:=Rows[P,H,9])then Print("rows {N}")else Print("bad")
    Print("after {H.N}")
    J:=holder{}
    if(N:=Rows[P,J,2])then Print("bad {N}")else Print("rejected {J.N}")
    Print("after {J.N}")
