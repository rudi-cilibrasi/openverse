# expect: F is defined twice with parameters a call cannot tell apart, (comparable_class) and (comparable)
# a <unique> class is comparable (Book of Verse ch. 11)
comparable_class := class<unique>{}
F(:comparable_class):void = {}
F(:comparable):void = {}
Main():void = {}
