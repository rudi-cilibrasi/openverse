# a class with a parent class below an interface that gives it fewer type
# arguments than its parent's: the root counts against the interface with the
# fewest anywhere below it (#209)
shower := interface:
    Show():string
container(t:type) := interface:
    Get():t
box(t:type) := class(container(t)):
    V:t
    Get<override>():t = V
sbox(t:type) := class(box(t), shower):
    Show<override>():string = "sbox"
Main():void =
    S:shower = sbox(int){V := 4}
    Print(S.Show())
