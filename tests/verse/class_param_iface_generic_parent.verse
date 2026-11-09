# a class with a parent class below an interface that gives it fewer type
# arguments than its parent's: the root counts against the interface with the
# fewest anywhere below it (#209)
shower := interface:
    Show():string
base(t:type) := class:
    V:t
child(t:type) := class(base(t), shower):
    Show<override>():string = "child"
Main():void =
    S:shower = child(int){V := 3}
    Print(S.Show())
