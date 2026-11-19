# What the rules for parametric var fields admit (#724): the class at a
# type (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, admits and runs
# followup-book2/parametric-var-where-construct-control: data 2), a type
# passed as an argument (the Book's tests, ParametricFunctions.versetest
# 442-470), a generic function whose type does not apply the class to its
# implicit type parameter, a parametric interface with a field that is not
# var and an interface that is not parametric with a var field (43.12
# admits parametric-interface-var-control and interface-var-field).
c(t:type) := class:
    var Data:t
Make(t:type, X:t)<transacts>:c(t) = c(t){Data := X}
Length(X:[]t where t:type):int = X.Length
i(t:type) := interface:
    Data:t
j := interface:
    var Count:int
counter := class(j):
    var Count<override>:int = 0
Main():void =
    Obj := c(int){Data := 1}
    set Obj.Data = 2
    Print("data {Obj.Data}")
    Made := Make(int, 3)
    set Made.Data += 1
    Print("made {Made.Data}")
    Print("length {Length(array{1, 2, 3})}")
    K := counter{}
    set K.Count = 5
    Print("count {K.Count}")
