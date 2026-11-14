# expect: so its value type must be persistable, and struct1 is not
# Book of Verse ch. 3: "The value type must be persistable"; weak_map.versetest:20 (3502)
class1 := class<unique><persistent><module_scoped_var_weak_map_key> {}
struct1 := struct {}
var Data:weak_map(class1, struct1) = map{}
Main():void = {}
