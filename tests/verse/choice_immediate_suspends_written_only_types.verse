pair(a:type,b:type) := class { A:a; B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }

Use(P:pair(a,b),Q:pair(c,d),Unused:t where a:type,b:type,c:type,d:type,t:type)<suspends>:void =
    Sleep(0.01)
    R:=for(A:=if(D:=dup[P]) then(D.C|D.C+1) else 0,B:=if(E:=dup[Q]) then(E.C|E.C+1) else 0):
        E:[]t=Concatenate()
        Print("{A} {B} {E.Length}")
        E
    Print("rows {R.Length}")
    Sleep(0.01)
Main()<suspends>:void =
    Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},7)
    Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},"witness")
