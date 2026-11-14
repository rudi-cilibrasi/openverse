# expect: set through a map's key can fail
class1 := class<module_scoped_var_weak_map_key><unique> {}
var X:weak_map(class1, int) = map{}
Main():void =
    set X[class1{}] = 1
