Note(S:string,N:int)<transacts>:int =
    Print(S)
    N
root(a:type,b:type) := interface:
    Picks(N:int, ?K:int = Note("root",1))<transacts>:int = N + K | N + K + 1
base(a:type,b:type) := class(root(a,b)):
    Picks<override>(N:int, ?K:int = Note("base",3))<transacts>:int = N + K + 10 | N + K + 20
fixed(u:type) := class(base(int,u)):
    Picks<override>(N:int, ?K:int = Note("fixed",4))<transacts>:int = N + K + 30 | N + K + 40
repeated(t:type) := class(base(t,t)):
    Picks<override>(N:int, ?K:int = Note("repeat",5))<transacts>:int = N + K + 60 | N + K + 70
reorder(x:type,y:type) := class(base(y,x)):
    Picks<override>(N:int, ?K:int = Note("reorder",6))<transacts>:int = N + K + 80 | N + K + 90
added(a:type,b:type,w:type) := class(base(a,b)):
    X:w
    Picks<override>(N:int, ?K:int = Note("added",7))<transacts>:int =
        E:[]w = Concatenate()
        N + K + E.Length + 100 | N + K + 110
plain := class(root(int,int)) {}
Run(P:root(a,b) where a:type,b:type)<transacts>:void =
    for (V := P.Picks(1)) { Print("v {V}") }
Main()<transacts>:void =
    Run(base(int,string){})
    Run(fixed(string){})
    Run(repeated(int){})
    Run(reorder(int,string){})
    Run(added(int,string,char){X:='c'})
    Run(plain{})
    for (V := fixed(string){}.Picks(1,?K:=9)) { Print("named {V}") }
