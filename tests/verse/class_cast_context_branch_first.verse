pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Pair(N:int where a:type,b:type):pair(a,b)=pair(a,b){}
Run(P:pair(a,b) where a:type,b:type)<suspends>:void=
    branch:
        Print("{if(V:=if(D:=dup[P])then(D.C|D.C+1)else 0)then V else -1}")
        Sleep(0.1)
    Sleep(0.2)
Main()<suspends>:void=Run(dup(int){})
