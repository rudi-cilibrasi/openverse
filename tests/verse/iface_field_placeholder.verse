# (run with --parametric-var-fields, openverse's extension: Epic's compiler refuses a generic function over a parametric class whose mutable data holds an implicit type parameter, or a var field in a parametric interface, UEFN 43.12 errors 3552 and 3502, #724)
# a for over objects of an interface whose field its classes give fixed types:
# the loop variable's placeholder gets the field at the interface's type
slot(t:type) := interface:
    var Item:t
    Show()<transacts>:string
islot := class(slot(int)):
    A:int = 0
    Show<override>()<transacts>:string = "i{Item}"
sslot := class(slot(string)):
    B:string = "b"
    C:int = 1
    Show<override>()<transacts>:string = "s{Item}"
base(t:type) := class(slot(t)):
    Z:int = 9
    Show<override>()<transacts>:string = "base"
Items(Ss:[]slot(t) where t:type)<transacts>:[]t = for (S : Ss) { S.Item }
Shows(Ss:[]slot(t) where t:type)<transacts>:[]string = for (S : Ss) { S.Show() }
Main():void =
    for (X : Items(array{islot{Item := 1}, islot{Item := 2}})) { Print("{X}") }
    for (X : Shows(array{sslot{Item := "a"}})) { Print(X) }
    for (X : Items(array{base(float){Item := 1.5}})) { Print("{X}") }
