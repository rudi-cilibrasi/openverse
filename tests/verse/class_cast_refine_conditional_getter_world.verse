# (run with --parametric-var-fields, openverse's extension: Epic's compiler refuses a generic function over a parametric class whose mutable data holds an implicit type parameter, or a var field in a parametric interface, UEFN 43.12 errors 3552 and 3502, #724)
box(t:type):=class:
    var A<getter(GetA)><setter(SetA)>:t=external{}
    var Stored:t
    var Reads:int=0
    GetA(:accessor)<transacts>:t=
        set Reads+=1
        Stored
    SetA(:accessor,V:t)<transacts>:void=set Stored=V
tight(t:subtype(comparable),u:subtype(comparable)):=class(box(t)){E:u}
Rows(P:box(t) where t:type)<transacts>:[]t=
    R:=for(V:=if(D:=tight[P])then(if(D.A=D.A,D.E=D.E)then(D.A|D.A)else D.A)else P.A){V}
    R
Control(P:box(t) where t:type)<transacts>:[]t=
    if(D:=tight[P])then(if(D.A=D.A,D.E=D.E)then array{D.A,D.A}else array{D.A})else array{P.A}
Main()<transacts>:void=
    A:=tight(int,string){Stored:=7,E:="x"}
    B:=tight(int,string){Stored:=7,E:="x"}
    R:=Rows(A)
    S:=Control(B)
    Print("all {R.Length} {A.Reads} {S.Length} {B.Reads}")
    C:=tight(int,string){Stored:=7,E:="x"}
    D:=tight(int,string){Stored:=7,E:="x"}
    if(Rows(C).Length=2)then Print("first {C.Reads}")else Print("bad")
    if(Control(D).Length=2)then Print("control {D.Reads}")else Print("bad")
    E:=tight(int,string){Stored:=7,E:="x"}
    F:=tight(int,string){Stored:=7,E:="x"}
    if(Rows(E).Length=9)then Print("bad")else Print("reject {E.Reads}")
    if(Control(F).Length=9)then Print("bad")else Print("control-reject {F.Reads}")
