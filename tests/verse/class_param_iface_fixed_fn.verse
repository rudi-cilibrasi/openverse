# a subclass fixing the root's dropped type argument to a function type: closed,
# so its plain interface does not make the root hide it (#276, #308 review)
shower := interface:
    Show():string
container(t:type) := interface:
    Get():t
box(t:type) := class(container(t)):
    V:t
    Get<override>():t = V
fbox := class(box(int->int), shower):
    Show<override>():string = "fbox {Get()(2)}"
Inc(X:int):int = X + 1
Main():void =
    S:shower = fbox{V := Inc}
    Print(S.Show())
    C:container(int->int) = fbox{V := Inc}
    Print("{C.Get()(5)}")
