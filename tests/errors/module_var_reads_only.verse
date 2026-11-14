# expect: F sets the module-scoped var X, which has the effect <writes>
class1 := class<module_scoped_var_weak_map_key><unique> {}
var X:weak_map(class1, int) = map{}
F(K:class1)<reads><decides>:void = set X[K] = 1
Main():void = {}
