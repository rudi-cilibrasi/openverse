# expect: sync needs at least two arms that can suspend
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Child(N:int)<suspends>:void=Sleep(0.2)
Wait(N:int)<suspends>:int=block{Sleep(0.1);N}
Use(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:int=
    R:=sync:
        block:
            if(D:=dup[P]):
                T:=spawn{Child(D.C)}
            0
        block:
            Sleep(0.1)
            1
    R(0)
Main()<suspends>:void=Print("result {Use(dup(int){},dup(string){})}")
