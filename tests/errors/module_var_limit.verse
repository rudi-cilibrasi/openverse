# expect: is one of 5 weak_maps keyed by <persistent> classes, and a program may have 4
# weak_map.versetest:648 (3502 for each)
class1 := class<unique><persistent><module_scoped_var_weak_map_key> {}
var X0:weak_map(class1, int) = map{}
var X1:weak_map(class1, int) = map{}
var X2:weak_map(class1, int) = map{}
var X3:weak_map(class1, int) = map{}
var X4:weak_map(class1, int) = map{}
Main():void = {}
