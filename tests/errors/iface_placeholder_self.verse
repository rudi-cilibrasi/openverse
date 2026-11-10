# expect: no class at or below node can be constructed without an instance of itself, so a variable or temporary of type node(t) has no initial value
# an interface field of the interface's own type: a placeholder at node(t)
# would have to hold itself (#157). No program can build a node either (each
# would need another first: no null, and a construction evaluates its fields
# before it makes the object), so only code that never runs with one is refused
node(t:type) := interface:
    Next:node(t)
    Get():t
ni := class(node(int)):
    V:int
    Get<override>():int = V
Gets(Ns:[]node(t) where t:type):[]t = for (N : Ns) { N.Get() }
Main():void = Print("ok")
