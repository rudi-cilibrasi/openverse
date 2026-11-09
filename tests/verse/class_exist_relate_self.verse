# an override that reads its type arguments from its receiver, dispatched
# to for a class whose pins relate them to further ones (#209)
ex(t:type) := class<abstract>:
    Eval():t
    Name():string = "ex"
lit := class(ex(int)):
    V:int
    Eval<override>():int = V
w1(a:type) := class(ex([]a)):
    E:ex(a)
    Eval<override>():[]a = array{E.Eval()}
w2(b:type) := class(w1(?b)):
    Name<override>():string = "w2"
Run(E:ex(int)):int = E.Eval()
Main():void = Print("{Run(lit{V := 1})}")
