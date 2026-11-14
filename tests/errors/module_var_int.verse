# expect: the module-scoped var Data has the type int: a module-scoped var must be a weak_map
# Book of Verse ch. 16, 18; weak_map.versetest:16, GlobalVariables.versetest:5 (3502)
var Data:int = 0
Main():void = {}
