# expect: var<private> on the module-scoped var X is not supported yet
class1 := class<module_scoped_var_weak_map_key><unique> {}
var<private> X:weak_map(class1, int) = map{}
Main():void = {}
