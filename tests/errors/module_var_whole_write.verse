# expect: the module-scoped var X is read and written one entry at a time
# weak_map.versetest:174 (3502)
class1 := class<module_scoped_var_weak_map_key><unique> {}
var X:weak_map(class1, int) = map{}
Main():void =
    set X = map{}
