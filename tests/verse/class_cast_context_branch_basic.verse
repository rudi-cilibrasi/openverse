pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Pair(N:int where a:type,b:type):pair(a,b)=pair(a,b){}
Run(P:pair(a,b) where a:type,b:type)<suspends>:void=
    branch:
        Print("{if(D:=dup[P])then D.C else 0}")
        Sleep(0.1)
    Sleep(0.2)
Main()<suspends>:void=Run(dup(int){})
