pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Use(P:pair(a,b) where a:type,b:type)<suspends>:int=
    R:=sync:
        block:
            if(D:=dup[P])then 4 else block{Sleep(0.1);0}
        block:
            Sleep(0.2)
            1
    R(0)
Main()<suspends>:void=Print("result {Use(dup(int){})}")
