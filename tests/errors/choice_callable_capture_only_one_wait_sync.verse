# expect: sync needs at least two arms that can suspend
Dup(X:t where t:type)<computes>:t=X|X
Keep(X:t where t:subtype(comparable))<computes>:int=if(X=X)then 1 else 0
ra:=class<computes>{K:int=1}
rb:=class<computes>{K:int=2}
IA(X:int)<suspends><computes>:ra=block{Sleep(0.0);ra{}}
SB(X:string)<suspends><computes>:rb=block{Sleep(0.0);rb{}}
ca:=class{V:int=7;F:type{_(:int)<suspends><computes>:ra}=IA}
cb:=class{V:string="s";F:type{_(:string)<suspends><computes>:rb}=SB}
Main()<suspends>:void=
    sync:
        block:
            Rows:=for(A:=(Dup(ca{})|Dup(cb{})),B:=(Dup(1)|Dup("s"))):block{F:=A.F;Keep(B)+1}
            var Total:int=0
            for(R:Rows):set Total+=R
            Print("{Rows.Length} {Total}")
        block:
            Sleep(0.0)
            Print("peer")
