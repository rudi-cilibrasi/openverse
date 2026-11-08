# a for over objects of an interface whose field its classes give fixed types:
# the loop variable's placeholder gets the field at the interface's type
slot(t:type) := interface:
    var Item:t
    Show():string
islot := class(slot(int)):
    A:int = 0
    Show<override>():string = "i{Item}"
sslot := class(slot(string)):
    B:string = "b"
    C:int = 1
    Show<override>():string = "s{Item}"
base(t:type) := class(slot(t)):
    Z:int = 9
    Show<override>():string = "base"
Items(Ss:[]slot(t) where t:type):[]t = for (S : Ss) { S.Item }
Shows(Ss:[]slot(t) where t:type):[]string = for (S : Ss) { S.Show() }
Main():void =
    for (X : Items(array{islot{Item := 1}, islot{Item := 2}})) { Print("{X}") }
    for (X : Shows(array{sslot{Item := "a"}})) { Print(X) }
    for (X : Items(array{base(float){Item := 1.5}})) { Print("{X}") }
