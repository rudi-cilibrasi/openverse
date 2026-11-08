# a class that fixes a type argument overrides a method an interface declares (#142)
container(t:type) := interface:
    Get():t
box(t:type) := class(container(t)):
    V:t
    Get<override>():t = V
int_box := class(box(int)):
    Get<override>():int = V + 1
GetC(C:container(t) where t:type):t = C.Get()
GetB(B:box(t) where t:type):t = B.Get()
Main():void =
    Print("{GetC(int_box{V := 1})}")
    Print("{GetC(box(int){V := 1})}")
    Print(GetC(box(string){V := "s"}))
    Print("{GetB(int_box{V := 5})}")
