vec := class<computes> { N:int }
operator'+'(A:vec, B:vec)<computes>:vec = vec{N:=A.N+B.N}
operator'+'(A:tuple(int,int), B:tuple(int,int))<computes>:int = A(0)*1000+A(1)*100+B(0)*10+B(1)
operator'+'(A:tuple(string,string), B:tuple(string,string))<computes>:string = A(0)+B(1)
Main():void =
    Print("custom {(1,2)+(3,4)}")
    Print(("a","b")+("c","d"))
    A := array{1,2}+(3,4)
    Print("native {A.Length}")
