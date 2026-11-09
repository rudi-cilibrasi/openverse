# expect: child has a parent class and lists shower, which gives it fewer type arguments than its root class's interfaces: not supported yet (#276)
shower := interface:
    Show():string
base(t:type) := class:
    V:t
child(t:type) := class(base(t), shower):
    Show<override>():string = "child"
Main():void =
    S:shower = child(int){V := 3}
    Print(S.Show())
