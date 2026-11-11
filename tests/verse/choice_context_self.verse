Two(N:int):int=N|N+1
base(t:type):=class:
    Data:t
    Echo(X:t)<computes>:t=X
child(u:type):=class(base(u)):
    var Copy:?u=false
    block:
        R:=for(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2))):
            (super:)Echo(Data)
        if(V:=R[0]):set Copy=option{V}
box(t:type):=class{Data:t;Copy:t}
Make<constructor>(X:t where t:type):=box(t):
    Data:=X
    Copy:=block:
        R:=for(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2))):X
        if(V:=R[0])then V else X
Main():void=
    if(X:=child(int){Data:=7}.Copy?):Print("int {X}")
    if(X:=child(string){Data:="class"}.Copy?):Print("string {X}")
    if(X:=child([]int){Data:=array{7,8}}.Copy?):Print("array {X.Length}")
    X:=Make((9,"ctor")).Copy
    Print("ctor {X(0)} {X(1)}")
