# expect: the module-scoped var b.ArrayOfA has the type []a
# GlobalVariables.versetest:39 (3502)
a := class:
    MyInt:int = 0
b := module:
    var ArrayOfA:[]a = array{}
Main():void = {}
