# Echo(:[]t) beside Echo(:int) in a class (#724): two overloads, as F(:a)
# beside F(:[]a) is (tests/verse/overload_scalar_array; the refusal this
# program pinned since #510 was openverse's own). With --function-coercions,
# as tests/verse/overload_audit_interface_value_scope.
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
