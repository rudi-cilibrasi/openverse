cell:=class{var N:int=0}
marker(t:type,u:type):=class:
    C:cell
    Size()<transacts>:int=
        set C.N+=1
        Print("size {C.N}")
        27+C.N
Touch(B:marker(a,b) where a:type,b:type)<transacts>:marker(a,b)=
    set B.C.N+=1
    Print("receiver {B.C.N}")
    B
Run(B:marker(a,b) where a:type,b:type)<transacts>:int=
    F:=Touch(B).Size
    A:=F()
    D:=F()
    A+D
Main():void=Print("result {Run(marker(int,string){C:=cell{}})}")
