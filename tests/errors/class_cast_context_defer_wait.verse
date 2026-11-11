# expect: Sleep suspends, and a defer cannot suspend (#156)
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Run(P:pair(a,b) where a:type,b:type)<suspends>:void=
    defer:if(D:=dup[P]):Sleep(0.1)
Main()<suspends>:void=Run(dup(int){})
