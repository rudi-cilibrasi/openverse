# expect: M.X is internal to M: mark it <public> to use it outside
class1 := class<module_scoped_var_weak_map_key><unique> {}
M := module:
    var X:weak_map(class1, int) = map{}
F(K:class1)<decides>:int = M.X[K]
Main():void = {}
