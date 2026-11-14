# expect: the module-scoped var M85.Scores is read and written one entry at a time
# Book of Verse ch. 3, its block 71 (3502)
k85 := class<unique><persistent><module_scoped_var_weak_map_key> {}
M85 := module:
    var Scores:weak_map(k85, int) = map{}
    GetAll()<transacts>:weak_map(k85, int) = Scores
Main():void = {}
