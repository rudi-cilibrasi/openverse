box(t:type) := class { A:t }
tight(t:type,u:type) := class(box(t)) { E:u }
RunTrue(P0:box(t0) where t0:type):int=
    R:=for(A0:=if(D:=tight[P0]) then (if(1=1) then(D.A|D.A) else D.A) else P0.A):
        A0
    R.Length

RunFalse(P0:box(t0) where t0:type):int=
    R:=for(A0:=if(D:=tight[P0]) then (if(1=0) then(D.A|D.A) else D.A) else P0.A):
        A0
    R.Length

RunEmpty(P0:box(t0) where t0:type):int=
    R:=for(A0:=if(D:=tight[P0]) then (if(1=0) then(D.A|D.A) else array{D.A}[1]) else P0.A):
        A0
    R.Length
Main():void=
    P:=tight(int,string){A:=1,E:="s"}
    Print("{RunTrue(P)}")
    Print("{RunFalse(P)}")
    Print("{RunEmpty(P)}")
    Print("{RunTrue(box(int){A:=1})}")
