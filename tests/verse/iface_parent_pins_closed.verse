# an interface without type parameters that gives its parent some (#53):
# intI := interface(container(int)) holds int, and classes below it, also a
# parametric one, are container(int)s
container(t:type) := interface:
    Get():t
intI := interface(container(int)):
    Twice():int
c := class(intI):
    Get<override>():int = 5
    Twice<override>():int = 10
cg(t:type) := class(intI):
    W:t
    Get<override>():int = 6
    Twice<override>():int = 12
G(C:container(u) where u:type):u = C.Get()
T(X:intI):int = X.Twice() + X.Get()
Main():void =
    Print("{G(c{})} {T(c{})} {G(cg(string){W := "w"})} {T(cg(logic){W := true})}")
