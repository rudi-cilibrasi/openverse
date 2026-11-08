# an omitted named default of an option of a class that every class below
# fixes otherwise: no temporary of that class is needed (#175)
cell(t:type) := class<abstract>:
    Value:t
    Get():t = Value
intcell := class(cell(int)):
    Get<override>():int = Value + 1
box(t:type) := class:
    V:t
    Get(X:t, ?O:?cell(string) = false):t = V
int_box := class(box(int)):
    Get<override>(X:int, ?O:?cell(string) = false):int = X
G(B:box(t), X:t where t:type):t = B.Get(X)
Main():void = Print("{G(int_box{V := 1}, 10)}")
