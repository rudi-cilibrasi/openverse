# expect: is keyed by class1, which is not a class with <module_scoped_var_weak_map_key>
# Book of Verse ch. 3; weak_map.versetest:26 (3502)
class1 := class<unique> {}
struct1 := struct<persistable> {}
var Data:weak_map(class1, struct1) = map{}
Main():void = {}
