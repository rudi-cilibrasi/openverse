# expect: these type values are together a subtype(class1), not a castable_subtype(class1)
class1 := class{}
class2 := class<castable>(class1){}
class3 := class<castable>(class1){}
Value:[]castable_subtype(class1) = array{class2, class3, class2}
Main():void = {}
