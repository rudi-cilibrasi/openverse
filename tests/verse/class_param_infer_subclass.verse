# (run with --parametric-var-fields, openverse's extension: Epic's compiler refuses a generic function over a parametric class whose mutable data holds an implicit type parameter, or a var field in a parametric interface, UEFN 43.12 errors 3552 and 3502, #724)
# regression test from the #39 review (p04_generic_infer_fixed)
cell(t:type) := class:
    var Value:t
intcell := class(cell(int)):
    Y:int = 0
Get(C:cell(t) where t:type):t = C.Value
Main():void =
    I := intcell{Value := 4}
    Print("{Get(I)}")
