# Each copied alternative chooses its own top-level overload (#283).
Two(N:int)<transacts>:int = N | N * 10
Two(S:string)<transacts>:string = S | S + "!"
Dup(V:t where t:type):t = V | V
Main():void =
    for (A := (Dup(1) | Dup("x")), B := Two(A)) { Print("{B}") }
    if (A := Dup(1) | Dup("x"), B := Two(A), B = "x!"): Print("first string")
    O := option{A := Dup(1) | Dup("x"); B := Two(A); B = "x!"; B}
    if (O? = "x!"): Print("option string")
