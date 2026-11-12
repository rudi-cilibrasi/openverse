# Last-generator staging must retain a nested body's array layer and writes.
Dup(X:t where t:type)<transacts>:t=X|X
Main()<suspends><transacts>:void=
    var N:int=0
    for(A:=(Dup(1)|Dup("s"))):
        for(X:=(Dup(A)|Dup(A)),Y:=(Dup(1)|Dup(2))):
            Sleep(0.0)
            set N+=Y
    Print("n {N}")
