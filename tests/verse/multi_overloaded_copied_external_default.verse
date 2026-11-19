Dup(V:t where t:type):t = V | V
Two(N:int)<transacts>:int = N | N + 1
Two(S:string)<transacts>:string = S | S + "!"
Size(?Xs:[]int=for(X:=Two(1)){X})<transacts>:int = Xs.Length
Pick(N:int)<transacts>:int = N | N + 10
Pick(S:string)<transacts>:int = S.Length | S.Length + 10
Main():void =
    for (A := Dup(1) | Dup("x"), B := Pick(A)): Print("{B} {Size()}")
    if (A := Dup(1) | Dup("x"), B := Pick(A), Size() = 2, B = 11): Print("first 2")
    O := option{A := Dup(1) | Dup("x"); B := Pick(A); Size() = 2; B = 11; B}
    if (X := O?): Print("option {X} 2")
