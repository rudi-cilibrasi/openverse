cell:=class{var N:int=0}
OldA(H:cell,X:int,Y:int)<reads><writes>:int=block{Print("old a");set H.N+=100;X+Y}
NewA(H:cell,X:int,Y:int)<reads><writes>:int=block{Print("new a");set H.N+=100;X+Y+1000}
OldB(H:cell,X:int,Y:int)<transacts>:int=block{Print("old b");set H.N+=100;X+Y}
NewB(H:cell,X:int,Y:int)<transacts>:int=block{Print("new b");set H.N+=100;X+Y+1000}
ca:=class:
    H:cell
    var F:type{_(:cell,:int,:int)<reads><writes>:int}
    Args()<transacts>:tuple(cell,int,int)=block{Print("args a");set H.N+=1;set F=NewA;(H,1,2)}
cb:=class:
    H:cell
    var F:type{_(:cell,:int,:int)<transacts>:int}
    Args()<transacts>:tuple(cell,int,int)=block{Print("args b");set H.N+=1;set F=NewB;(H,4,5)}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    H:=cell{}
    P:=ca{H:=H,F:=OldA}
    Q:=cb{H:=H,F:=OldB}
    Rows:=for(A:=(Dup(P)|Dup(Q))):
        V:=A.F(A.Args())
        Print("row {V} {H.N}")
        V
    Print("done {Rows.Length} {H.N}")
