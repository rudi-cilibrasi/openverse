Dup(V:t where t:type):t = V | V
Mix(N:int)<transacts>:int = N | N + 1
Mix(S:string)<transacts>:int = 7
Main():void =
    for (A := Dup(1) | Dup("s"), B := Mix(A)): Print("{B}")
    if (A := Dup(1) | Dup("s"), B := Mix(A), B = 7): Print("first {B}")
    O := option{A := Dup(1) | Dup("s"); B := Mix(A); B = 7; B}
    if (B := O?): Print("option {B}")
