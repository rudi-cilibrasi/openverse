# classes with type parameters of their own, which the type arguments they
# give their parent do not give as a whole, override: a dispatch on the
# parent opens them (#209)
base(t:type) := class:
    Value:t
    Get():t = Value
    Tag():string = "base"
pair(t:type, u:type) := class(base(t)):
    Other:u
    Get<override>():t = Value
    Tag<override>():string = "pair"
box(t:type) := class:
    V:t
    Get():t = V
arr_box(u:type) := class(box([]u)):
    E:u
    Get<override>():[]u = array{E, E}
pair2(t:type, u:type) := class:
    A:t
    B:u
    Get():t = A
nest(t:type) := class(pair2(?t, ?t)):
    Get<override>():?t = B
Show(B:base(t) where t:type):string = B.Tag()
Size(B:box([]t) where t:type):int = B.Get().Length
First(P:pair2(t, u) where t:type, u:type):t = P.Get()
Main():void =
    Print(Show(pair(int, string){Value := 1, Other := "o"}))
    Print(Show(base(int){Value := 2}))
    Print("{Size(arr_box(int){V := array{}, E := 3})} {Size(box([]int){V := array{1, 2, 3}})}")
    if (X := First(nest(int){A := false, B := option{4}})?) then Print("{X}")
