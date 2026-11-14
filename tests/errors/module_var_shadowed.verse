# expect: 'X' is already the name of a module-scoped var
class1 := class<module_scoped_var_weak_map_key><unique> {}
var X:weak_map(class1, int) = map{}
Main():void =
    X := 3
