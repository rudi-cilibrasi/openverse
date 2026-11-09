# expect: sbox has a parent class and is below shower, which gives it fewer type arguments than its root class does: not supported yet (#276)
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
