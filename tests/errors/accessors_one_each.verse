# expect: X is a field with accessors: it has one <getter(…)> and one <setter(…)>
c := class:
    var X<getter(GetX)>:int = external{}
    GetX(:accessor):int = 0
Main():void = {}
