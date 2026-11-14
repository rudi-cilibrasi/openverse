# expect: F reads the module-scoped var X, which has the effect <reads>
class1 := class<module_scoped_var_weak_map_key><unique> {}
var X:weak_map(class1, int) = map{}
F(K:class1)<computes><decides>:int = X[K]
Main():void = {}
