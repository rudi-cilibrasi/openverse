# What the rule for parametric mutable data admits (#724): a generic
# function that constructs c(t) in its body only, its type not mentioning c
# (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, admits
# followup-book3/parametric-var-where-local), and a parametric class whose
# var field does not mention its parameter (admits parametric-var-other-field).
c(t:type) := class:
    var Data:t
F(X:t where t:type)<transacts>:int =
    Obj := c(t){Data := X}
    1
d(t:type) := class:
    var Count:int = 0
    Data:t
G(X:t where t:type)<transacts>:d(t) = d(t){Data := X}
Main():void =
    Print("result {F(7)}")
    Obj := G(1)
    set Obj.Count = 2
    Print("count {Obj.Count}")
