# expect: and sink has fields: references to it through views cannot read them yet (#351)
# an interface referred to through views (both gives sink its second type
# argument) with a field, which would be at another place in each class
container(t:type) := interface:
    Get():t
sink(u:type) := interface:
    var Count:int
    Put(X:u):int
both(t:type, u:type) := class(container(t), sink(u)):
    V:t
    var Count<override>:int = 0
    Get<override>():t = V
    Put<override>(X:u):int = Count
Main():void = Print("x")
