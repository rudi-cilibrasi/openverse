# expect: starts as map{} in openverse: an initial value with entries is not supported yet
class1 := class<module_scoped_var_weak_map_key><unique> {}
Make():class1 = class1{}
var X:weak_map(class1, int) = map{Make() => 1}
Main():void = {}
