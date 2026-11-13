# Fors nested in each other, each with a refining choice as its clause, and a
# return from the innermost body (#335, #437): each for's continuation is
# keyed by what its code uses, so it is made once wherever it is first asked
# for (the return's local is named by its place, not by the locals in scope).
# In an interface's default at two type arguments, a generic class's method
# that sets a var, and a <suspends> function.
pair(a:type,b:type) := class { A:a; B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
Two(N:int):int=N|N+1
finder(t:type) := interface:
    Find(P:pair(a,b),Q:pair(c,d),X:t where a:type,b:type,c:type,d:type):int =
        for(V0:=if(D:=dup[P])then(D.C|D.C+1)else 0):
            for(V1:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
                for(V2:=if(F:=dup[P])then(F.C|F.C+1)else 0):
                    W:[]t=array{X}
                    if(V0+V1+V2>13):
                        return V0+V1+V2+W.Length
        -1
f1 := class(finder(int)){}
f2 := class(finder(string)){}
holder(t:type) := class:
    X:t
    Walk(P:pair(a,b) where a:type,b:type):int =
        var Seen:[]t = array{}
        for(V0:=if(D:=dup[P])then(D.C|D.C+1)else 0):
            for(V1:=if(E:=dup[P])then(E.C|E.C+1)else 0):
                set Seen += array{X}
                if(V0+V1>9):
                    return V0+V1+Seen.Length
        -1
Wait(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:int=
    var Total:int=0
    for(V0:=if(D:=dup[P])then(D.C|D.C+1)else 0):
        for(V1:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
            for(V2:=(Two(0)|Two(2))):
                Sleep(0.0)
                set Total+=V0+V1+V2
                if(Total>30):
                    return Total
    Total
Main()<suspends>:void=
    S1:finder(int)=f1{}
    S2:finder(string)=f2{}
    Print("{S1.Find(dup(int){A:=1,B:=2},dup(int){A:=1,B:=2},3)} {S2.Find(dup(int){A:=1,B:=2},pair(int,string){A:=1,B:="x"},"s")} {f2{}.Find(dup(string){A:="a",B:="b"},dup(int){A:=1,B:=2},"t")}")
    Print("{holder(int){X:=1}.Walk(dup(int){A:=1,B:=2})} {holder(string){X:="s"}.Walk(dup(string){A:="a",B:="b"})} {holder(int){X:=1}.Walk(pair(int,string){A:=1,B:="x"})}")
    Print("{Wait(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})} {Wait(pair(int,string){A:=1,B:="x"},dup(int){A:=1,B:=2})}")
