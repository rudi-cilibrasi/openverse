# expect: spawn in a defer is not supported (#156)
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Child(N:int)<suspends>:void=Sleep(0.1)
Run(P:pair(a,b) where a:type,b:type)<suspends>:void=
    defer:if(D:=dup[P]):spawn{Child(D.C)}
Main()<suspends>:void=Run(dup(int){})
