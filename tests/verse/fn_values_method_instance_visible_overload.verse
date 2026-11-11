base:=class:
    Make(N:int where u:type):[]u=array{}
    Bind(X:t where t:type):type{_(:int):[]t}=Make
child:=class(base):
    Make(S:string where v:type):[]v=array{}
Main():void=
    B:base=child{}
    F:type{_(:int):[]string}=B.Make
    G:=B.Bind(7)
    Print("{F(3).Length} {G(4).Length}")
