# regression test from the #39 review (e09_fixed_chain)
cell(t:type) := class:
    var Value:t
intcell := class(cell(int)):
    Describe():string = "intcell {Value}"
special := class(intcell):
    Describe<override>():string = "special {Value}"
Main():void =
    I:intcell = special{Value := 1}
    Print(I.Describe())
