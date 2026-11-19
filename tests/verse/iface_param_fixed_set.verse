# (run with --parametric-var-fields, openverse's extension: Epic's compiler refuses a generic function over a parametric class whose mutable data holds an implicit type parameter, or a var field in a parametric interface, UEFN 43.12 errors 3552 and 3502, #724)
# regression test from the #53 review (p67)
holder(t:type) := interface:
    var Item:t
box(t:type) := class(holder(t)):
    N:int = 0
intbox := class(holder(int)):
    M:int = 0
Put(H:holder(t), X:t where t:type):void = set H.Item = X
Main():void =
    B := intbox{Item := 1}
    Put(B, 9)
    Print("{B.Item}")
