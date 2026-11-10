# expect: and q has a parent class, p, which does not reach container: a class with a parent class that adds such an interface is not supported yet (#351)
# a class with a class parent that lists an interface at type arguments
# not a prefix of its own: its hidden fields, which a dispatch through a
# view reads, are only for a class without a class parent
container(t:type) := interface:
    Get():t
sink(u:type) := interface:
    Put(X:u):int
p(t:type) := class(sink(t)):
    Put<override>(X:t):int = 1
q(u:type, t:type) := class(p(u), container(t)):
    V:t
    Get<override>():t = V
Main():void =
    C:container(string) = q(int, string){V := "v"}
    Print(C.Get())
