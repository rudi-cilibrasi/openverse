root(t:type):=class{}
extra(t:type,u:type):=class(root(t)){C:int=9}
Use(P:root(t),Hit:logic where t:type)<suspends>:void=
    defer:Print("source")
    sync:
        block:
            if(D:=extra[P]):
                branch:
                    defer:Print("A {D.C}")
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
            Sleep(0.2)
    Print("joined")
Main()<suspends>:void=Use(extra(int,string){},true)
