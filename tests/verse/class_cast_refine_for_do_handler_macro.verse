pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){}
holder:=class{var N:int=0}
Touch(H:holder,Reject:int)<transacts><decides>:int=
    set H.N+=1
    Print("touch {H.N}")
    H.N<>Reject
    H.N
Rows(P:pair(a,b),H:holder where a:type,b:type):[]int=
    for{V:=if(D:=dup[P])then(D.A|D.B)else P.B} do if(Touch[H,2])then 1 else 0
Main():void=
    H:=holder{}
    for(N:Rows(dup(int){A:=1,B:=2},H)){Print("row {N}")}
    Print("after {H.N}")
