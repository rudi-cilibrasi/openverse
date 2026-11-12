# expect: box has overloads of Echo a call cannot tell apart
source(t:type):=interface:
    Echo(X:t)<computes>:t
nested(t:type):=interface(source([]t)):
    Bind()<computes>:type{_(:[]t)<computes>:[]t}=Echo
box(t:type):=class(nested(t)):
    Echo<override>(X:[]t)<computes>:[]t=X
    Echo(X:int)<computes>:int=X+1
Main():void=
    F:=box(string){}.Bind()
    Print("{F(array{"value"}).Length}")
