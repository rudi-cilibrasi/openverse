# expect: var Data:t has no value: a declaration of a variable defined elsewhere
# valid syntax (Pointers.versetest:4: "var x:int"), and refused: openverse has no
# variables defined elsewhere
class1 := class<module_scoped_var_weak_map_key><unique> {}
var Data:weak_map(class1, int)
Main():void = {}
