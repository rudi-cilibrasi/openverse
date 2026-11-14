# An interface's overloaded methods with defaults (Book of Verse ch. 6,
# "Interfaces with Overloaded Methods"): a class overrides one overload and
# keeps the other's default, reached directly, through the interface and
# from code generic over a parametric one
shower := interface:
    Show(X:int):string = "int {X}"
    Show(X:string):string = "string {X}"
plain := class(shower) {}
own := class(shower):
    Show<override>(X:int):string = "own {X}"
container(t:type) := interface:
    Get():t
    Get(N:int):[]t = for (I := 1..N) { Get() }
box(a:type) := class(container(a)):
    X:a
    Get<override>():a = X
G(C:container(u), N:int where u:type):[]u = C.Get(N)
Main():void =
    S:shower = own{}
    Print("{plain{}.Show(1)} {plain{}.Show("a")} {own{}.Show(2)} {S.Show("b")}")
    B := box(int){X := 1}
    Print("{B.Get()} {B.Get(3).Length} {G(B, 2).Length}")
