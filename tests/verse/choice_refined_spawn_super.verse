pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
base(t:type) := class:
    Data:t
    Run(X:u,?E:[]t=Concatenate() where u:type)<suspends>:tuple(t,u,int)=
        Print("base {E.Length}")
        Sleep(0.1)
        (Data,X,E.Length)
child(v:type) := class(base(v)):
    Run<override>(X:u,?E:[]v=Concatenate() where u:type)<suspends>:tuple(v,u,int)=
        Print("override")
        Sleep(0.1)
        (Data,X,99)
    Start(P:pair(a,b),Z:u where a:type,b:type,u:type):[]task(tuple(v,u,int))=
        for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):
            spawn{(super:)Run(Z)}
Main()<suspends>:void=
    Tasks:=child(int){Data:=7}.Start(dup(string){A:="a",B:="b"},"x")
    Print("tasks {Tasks.Length}")
    for(T:Tasks):
        R:=T.Await()
        Print("result {R(0)} {R(1)} {R(2)}")
