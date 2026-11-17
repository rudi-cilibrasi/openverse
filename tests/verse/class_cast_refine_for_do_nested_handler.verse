box(t:type):=class{A:t}
tight(t:type,u:type):=class(box(t)){E:u}
Run(P:box(t) where t:type)<decides><transacts>:int=
    R:=for(A:=if(D:=tight[P])then(D.A|D.A)else P.A) do if(Z:=for(J:array{0}) do J>0)then Print("bad")else Print("local else")
    R.Length
Main()<decides><transacts>:void=Print("rows {Run[tight(int,string){A:=1,E:="s"}]}")
