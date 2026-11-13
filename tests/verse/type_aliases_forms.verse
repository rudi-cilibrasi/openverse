# Type aliases beside the forms that begin with `(` and the built-ins as
# values: `whole := (int)` is an alias, `(T){…}` constructs through one, a
# destructured tuple's elements take aliases' types, and `Root:float->float =
# Sqrt` is a constant, a built-in's value (a constant states its type, ch. 16)
whole := (int)
pt := tuple(int, string)
box(t:type) := class:
    V:t
box_of(t:type) := box(t)
int_box := box(int)
point := struct:
    X:int
    Y:int
pt2 := point
Root:float->float = Sqrt
Apply(F(:float):float, X:float):float = F(X)
Pair():pt = (3, "three")
Main():void =
    W:whole = 5
    (A:whole, _) = Pair()
    (_, B:string) = Pair()
    C := (int_box){V := 7}
    D := (box_of(string)){V := "d"}
    E := (pt2){X := 1, Y := 2}
    Print("{W} {A} {B} {C.V} {D.V} {E.X + E.Y}")
    Print("{Root(9.0)} {Sgn(3)} {Clamp(9, 0, 5)} {Apply(Sqrt, 16.0)}")
    Print("{let{K := 2} do K * W}")
