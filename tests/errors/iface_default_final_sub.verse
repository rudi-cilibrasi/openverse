# expect: box.Get is <final>: it cannot be overridden
# (the copy of c2's <final> Get in box keeps it final for classes below, #53)
container(t:type) := interface:
    Get():t
c2(t:type) := interface(container([]t)):
    V():t
    Get<override><final>():[]t = array{V(), V()}
box(a:type) := class(c2(a)):
    X:a
    V<override>():a = X
sub(a:type) := class(box(a)):
    Get<override>():[]a = array{}
Main():void = Print("x")
