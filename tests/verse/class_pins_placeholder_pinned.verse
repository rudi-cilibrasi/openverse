# a placeholder below a generic abstract class that itself records pins (#157)
a(t:type) := class<abstract>:
    V:t
    Get():t = V
b := class<abstract>(a(int)):
    Get<override>():int = V + 1
b2(u:type) := class<abstract>(b):
    U:u
c := class(b2(string)):
    W:int = 0
GU(X:?b2(u), D:u where u:type):u = if (Y := X?) then Y.U else D
Main():void = Print(GU(option{c{V := 1, U := "u"}}, "d"))
