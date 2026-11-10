# expect: no class at or below n can be constructed without an instance of itself, so a variable or temporary of type n(t) has no initial value
# a placeholder that would hold one at a bigger type, through two
# hierarchies below the interface: refused at once, not after trying every
# placeholder at every size (#157); an n(t) would need an n([]t) first, so no
# program can build one either
n(t:type) := interface:
    Next:n([]t)
    Get():t
c1(t:type) := class<abstract>(n(t)):
    X1:int = 0
d1 := class(c1(int)):
    Get<override>():int = 1
c2(t:type) := class<abstract>(n(t)):
    X2:int = 0
d2 := class(c2(int)):
    Get<override>():int = 2
Gets(Ns:[]n(t) where t:type):[]t = for (N : Ns) { N.Get() }
Main():void = Print("ok")
