# expect: c implements pi at two instances, pi(string) and pi(int), through the interfaces it lists
# (main accepted the class, but did not treat it as a pi(int))
pi(t:type) := interface:
    Get():t
c := class(pi(string), pi(int)):
    Get<override>():string = "s"
GI(X:pi(int)):int = X.Get()
Main():void =
    Print("{GI(c{})}")
