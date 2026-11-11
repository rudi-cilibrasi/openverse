root:=class{}
extra(t:type):=class(root){X:t}
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){}
Global:root=extra(string){X:="global"}
Id(X:t where t:type)<computes>:t=X
Run(P:root,X:a,Y:b,?N:int=block{W:[]a=Concatenate();if(D:=extra[P])then Id(array{D.X}).Length+W.Length else 0} where a:type,b:type):int=N
box(a:type,b:type):=class:
    X:a
    Y:b
    N:int=block{P:root=Global;W:[]b=Concatenate();if(D:=extra[P])then Id(array{D.X}).Length+W.Length else 0}
Make(X:a,Y:b where a:type,b:type):int=box(a,b){X:=X,Y:=Y}.N
Main():void=
    Print("{Run(extra(string){X:="s"},7,"x")} {Run(extra(int){X:=8},"y",9)} {Run(root{},7,"s")}")
    Print("{Make(7,"s")} {Make("x",9)}")
