pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Pair(N:int where a:type,b:type):pair(a,b)=pair(a,b){}
Run(P:pair(a,b) where a:type,b:type)<suspends>:int=
    R:=rush:
        block:
            N:=block{R:=for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):V;R.Length}
            Sleep(0.1)
            N
        block:
            Sleep(0.2)
            -1
    R
Main()<suspends>:void=Print("{Run(dup(int){})}")
