vec := class<computes> { N:int }
operator'+'(A:vec, B:vec)<computes>:vec = vec{N:=A.N+B.N}
Pair(Tag:string, N:int):tuple(int, int) = block{Print(Tag);(N,N+1)}
Main():void =
    A := Pair("left",1) + Pair("right",3)
    Print("pair {A.Length}")
    B := () + A + ()
    Print("unit {B.Length}")
    U:true = false
    C := U + A
    Print("true {C.Length}")
    D := A + (5,6) + (7,8)
    Print("chain {D.Length}")
    Long := (1,2)+(3,4)+(5,6)+(7,8)+(9,10)+(11,12)+(13,14)+(15,16)+(17,18)+(19,20)+(21,22)+(23,24)
    Print("long {Long.Length}")
    V := vec{N:=2} + vec{N:=3}
    Print("vec {V.N}")
