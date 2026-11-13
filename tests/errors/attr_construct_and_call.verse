# expect: an attribute is a class's value, constructed with {…}, or a constructor's call (…), not both
@attribscope_data
key := class<computes>(attribute) {}
@key(1){}
X:int = 0
Main():void = {}
