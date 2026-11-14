pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
start_probe := struct{}
base(t:type) := class:
    Data:t
    Run(X:string,?E:[]t=Concatenate())<suspends>:tuple(t,string,int)=
        Print("base {E.Length}")
        Sleep(0.1)
        (Data,X,E.Length)
    # ((super:)M is only in an override of M, the Book's rule: the methods
    # that call it are overloads of M that override these)
    Run(Probe:start_probe,P:pair(a,b),Z:string where a:type,b:type):[]task(tuple(t,string,int))=array{}
child(v:type) := class(base(v)):
    Run<override>(X:string,?E:[]v=Concatenate())<suspends>:tuple(v,string,int)=
        Print("override")
        Sleep(0.1)
        (Data,X,99)
    Run<override>(Probe:start_probe,P:pair(a,b),Z:string where a:type,b:type):[]task(tuple(v,string,int))=
        for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):
            spawn{(super:)Run(Z)}
Main()<suspends>:void=
    Tasks:=child(int){Data:=7}.Run(start_probe{},dup(string){A:="a",B:="b"},"x")
    Print("tasks {Tasks.Length}")
    for(T:Tasks):
        R:=T.Await()
        Print("result {R(0)} {R(1)} {R(2)}")
