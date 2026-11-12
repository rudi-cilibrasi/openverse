cell:=class{var N:int=0}
ca:=class:
    H:cell
    var Data:?[]int=option{array{1}}
    Refill()<transacts>:int=block{Print("refill");set H.N+=1;set Data=option{array{100}};2}
cb:=class:
    H:cell
    var Data:?[]int=option{array{10}}
    Refill()<transacts>:int=block{Print("refill");set H.N+=1;set Data=option{array{100}};2}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    H:=cell{}
    P:=ca{H:=H}
    Q:=cb{H:=H}
    Rows:=for(A:=(Dup(P)|Dup(Q)),R:=set A.Data?[0]+=(1|A.Refill())):
        Print("body {R}")
        set A.Data=false
        R
    Print("{Rows.Length} {H.N}")
