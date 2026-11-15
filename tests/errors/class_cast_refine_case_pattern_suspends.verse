# expect: suspends, and a failure context
# A cast in a computed pattern cannot hide a suspending method call.
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)):
    Get()<suspends>:int=(Sleep(0.0);4)
F(P:pair(a,b) where a:type,b:type)<suspends>:int=
    case(4):
        dup[P].Get() => 1
        _ => 2
Main()<suspends>:void=Print("{F(dup(int){})}")
