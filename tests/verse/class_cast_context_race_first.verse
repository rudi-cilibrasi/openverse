pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Run(P:pair(a,b) where a:type,b:type)<suspends>:int=
    R:=race:
        block:
            N:=if(V:=if(D:=dup[P])then(D.C|D.C+1)else 0)then V else -1
            Sleep(0.1)
            N
        block:
            Sleep(0.2)
            -1
    R
Main()<suspends>:void=Print("{Run(dup(int){})}")
