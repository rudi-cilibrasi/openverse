Two(N:int)<computes>:int=N|N+1
Early(N:int)<computes>:int=
    if(N<0):return 0
    N|N+1
Dup(V:t where t:type):t=V|V
Show(V:int):string="int {V}"
Show(V:string):string="string {V}"
Main()<suspends>:void=
    for(A:=(Dup(1)|Dup("x")),B:=(Two(10)|Two(20))):
        Sleep(0.0)
        Print("fallback {B}")
