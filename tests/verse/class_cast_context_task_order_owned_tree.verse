pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Use(P:pair(a,b),R:pair(c,d),Hit:logic where a:type,b:type,c:type,d:type)<suspends>:void=
    defer:Print("source")
    sync:
        block:
            if(D:=dup[P]):
                branch:
                    defer:Print("A {D.C}")
                    Sleep(0.25)
                    if(E:=dup[R]):
                        branch:
                            defer:Print("AA {E.C}")
                            Sleep(10.0)
                    Sleep(10.0)
                Sleep(0.2)
                branch:
                    defer:Print("B {D.C}")
                    Sleep(10.0)
        block:
            Sleep(0.1)
            branch:
                defer:Print("C")
                Sleep(10.0)
            Sleep(0.25)
    Print("joined")
Main()<suspends>:void=Use(dup(int){},dup(string){},true)
