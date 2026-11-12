# Reading a suspending callable is immediate; only invoking it needs a wait.
Dup(X:t where t:type)<computes>:t=X|X
Keep(X:t where t:subtype(comparable))<computes>:int=if(X=X)then 1 else 0
Hold(F:t where t:type)<computes>:int=1
ra:=class<computes>{K:int=1}
rb:=class<computes>{K:int=2}
IA(X:int)<suspends><computes>:ra=block{Sleep(0.0);ra{}}
SB(X:string)<suspends><computes>:rb=block{Sleep(0.0);rb{}}
ca:=class{F:type{_(:int)<suspends><computes>:ra}=IA}
cb:=class{F:type{_(:string)<suspends><computes>:rb}=SB}
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),B:=(Dup(1)|Dup("s"))):Hold(A.F)+Keep(B)
    var Total:int=0
    for(R:Rows):set Total+=R
    Print("{Rows.Length} {Total}")
