# (run with --parametric-var-fields, openverse's extension: Epic's compiler refuses a generic function over a parametric class whose mutable data holds an implicit type parameter, or a var field in a parametric interface, UEFN 43.12 errors 3552 and 3502, #724)
cell:=class{var N:int=0}
box(t:type):=class:
    var V:t
    C:cell
    Read()<reads>:tuple(t,int)=(V,C.N)
Touch(B:box(t) where t:type):box(t)=
    set B.C.N+=1
    Print("receiver {B.C.N}")
    B
Bind(B:box(t) where t:type):type{_()<reads>:tuple(t,rational)}=Touch(B).Read
Main():void=
    B:=box(string){V:="old",C:=cell{}}
    F:=Bind(B)
    set B.V="new"
    A:=F()
    set B.C.N+=1
    Z:=F()
    Print("{A(0)} {Floor(A(1))} {Z(0)} {Floor(Z(1))}")
