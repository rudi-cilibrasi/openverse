# expect: would name what is unknown (#250)
# A case arm cannot export an existential type opened by its local cast.
expr(t:type) := class<abstract>:
    Tag():string
lit := class(expr(int)):
    V:int
    Tag<override>():string = "lit"
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Tag<override>():string = "pair"
LeftTag(E:expr(t) where t:type)<transacts><decides>:string =
    X := case(1){1 => option{pairE[E].L}, _ => false}
    if (L := X?) then L.Tag() else "none"
Main():void =
    if(V:=LeftTag[pairE(int, int){L := lit{V := 4}, R := lit{V := 5}}]) then Print(V)
