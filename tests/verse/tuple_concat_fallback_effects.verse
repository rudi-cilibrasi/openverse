operator'+'(A:tuple(string,string), B:tuple(string,string))<transacts>:string =
    Print("custom")
    A(0)+B(1)
Concat()<computes>:int =
    A := (1,2)+(3,4)
    A.Length
Main():void =
    Print("native {Concat()}")
    Print(("a","b")+("c","d"))
