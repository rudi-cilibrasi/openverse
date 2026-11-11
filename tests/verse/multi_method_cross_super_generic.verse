# Class and method type parameters keep their source scope through super.
base(a:type,b:type) := class:
    A:a
    B:b
    Pack(X:v,Y:w,?Z:v=X,?Empty:[]w=Concatenate() where v:type,w:type)<transacts>:tuple(a,b,v,w,int) =
        (A,B,Z,Y,Empty.Length)
mid(x:type,y:type) := class(base(y,x)):
    Values(X:r,Y:s where r:type,s:type)<transacts>:tuple(y,x,r,s,int) =
        (super:)Pack(X,Y)|(super:)Pack(X,Y,?Z:=X,?Empty:=array{Y})
leaf(c:type,d:type) := class(mid(c,d)) {}
All(C:leaf(u,v),X:r,Y:s where u:type,v:type,r:type,s:type):[]tuple(v,u,r,s,int) =
    for(V:=C.Values(X,Y)): V
Main():void =
    C:=leaf(int,string){A:="a",B:=7}
    for(V:All(C,'x',9)): Print("{V(0)} {V(1)} {V(2)} {V(3)} {V(4)}")
