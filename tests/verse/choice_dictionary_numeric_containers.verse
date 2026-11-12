ca:=class{var Items:[]int=array{};var Value:?int=false}
cb:=class{var Items:[]rational=array{};var Value:?rational=false}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    P:=ca{}
    Q:=cb{}
    Rows:=for(A:=(Dup(P)|Dup(Q))):
        set A.Items=array{3,4}
        set A.Value=option{5}
        A.Items.Length
    var Total:int=0
    for(Row:Rows):set Total+=Row
    Print("{Rows.Length} {Total}")
    if(X:=P.Items[0],Y:=P.Items[1],Z:=P.Value?):Print("p {X} {Y} {Z}")
    if(X:=Q.Items[0],Y:=Q.Items[1],Z:=Q.Value?,X=3,Y=4,Z=5)then Print("q ok") else Print("bad")
