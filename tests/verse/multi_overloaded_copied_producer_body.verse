Dup(V:t where t:type):t = V | V
Two(N:int):int = N | N + 1
Two(S:string):string = S | S + "!"
Pick(N:int):int = N | N + 10
Pick(S:string):int = S.Length | S.Length + 10
Main():void =
    for (A := Dup(1) | Two("x"), B := Pick(A)):
        for (C := Pick(A)): Print("{B} {C}")
