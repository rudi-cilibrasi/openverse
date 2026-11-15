Dup(V:t where t:type):t = V | V
Many():int = 1 | 2
Pick(N:int,?D:[]int=for(X:=Many()){X}):int = N + D.Length | N + D.Length + 10
Pick(S:string,?D:[]int=for(X:=Many()){X}):int = 100 + D.Length | 110 + D.Length
Main():void =
    for (A := Dup(1) | Dup("x"), B := Pick(A)): Print("{B}")
