# expect: field 'Next' of n names n([]t), n at other type arguments than its own: a parametric type refers to itself only as n(t)
# an interface whose field needs an n([]t) for an n(t), so one at ever
# bigger types: polymorphic recursion, which the Book refuses where the type
# is defined (ch. 10, "Disallowed: Polymorphic Recursion"); no program could
# build one either, and the placeholder that would stand for it (#157) is
# never tried
n(t:type) := interface:
    Next:n([]t)
    Get():t
c1(t:type) := class<abstract>(n(t)):
    X1:int = 0
d1 := class(c1(int)):
    Get<override>():int = 1
Gets(Ns:[]n(t) where t:type):[]t = for (N : Ns) { N.Get() }
Main():void = Print("ok")
