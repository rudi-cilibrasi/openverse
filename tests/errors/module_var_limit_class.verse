# expect: at that limit one of them must have a class value
# weak_map.versetest:631, "Fail due to none of the value types being a class" (3502 for each)
class1 := class<unique><persistent><module_scoped_var_weak_map_key> {}
var X0:weak_map(class1, int) = map{}
var X1:weak_map(class1, int) = map{}
var X2:weak_map(class1, int) = map{}
var X3:weak_map(class1, int) = map{}
Main():void = {}
