# expect: so its value type must be persistable, and difficulty is not
# (Book of Verse ch. 3, ch. 17: a <persistent> key's weak map holds values
# that persist, and an enum persists only when it is <persistable>)
difficulty := enum{Easy, Hard}
key := class<unique><persistent><module_scoped_var_weak_map_key>:
    Id:int = 0
var Levels:weak_map(key, difficulty) = map{}
Main():void = {}
