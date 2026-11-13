# expect: <abstract> is not allowed on a method: it is for a class
# (a method with no body is abstract: only a class is marked <abstract>)
shape := class<abstract>:
    Area<abstract>():int
Main():void = {}
