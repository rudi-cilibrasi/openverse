# Method overriding, (super:) calls, and dispatch through a parent-typed
# value and inside the parent's own methods.
# Tests LANGUAGE.md, Supported, Classes: "<override>, <final>, (super:),
# virtual dispatch"; Classes: "This is virtual dispatch, also inside a
# method; (super:) uses the same rule".
# OpenVerse prints (Lean and C agree):
#   shape / I am shape | square / I am square | tile/square / I am tile/square
shape_cls := class:
    Name()<computes>:string = "shape"
    Describe()<computes>:string = "I am " + Name()

square_cls := class(shape_cls):
    Name<override>()<computes>:string = "square"

tile_cls := class(square_cls):
    Name<override>()<computes>:string = "tile/" + (super:)Name()

Main():void =
    Shapes:[]shape_cls = array{shape_cls{}, square_cls{}, tile_cls{}}
    for (S : Shapes):
        Print("OVPROBE {S.Name()} / {S.Describe()}")
