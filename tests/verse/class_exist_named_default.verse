# an omitted named argument whose default has no type of its own (false,
# array{}, map{}) in a dispatch that opens type arguments: its temporary has
# the method's declared type at the receiver's type arguments (#209)
expr(t:type) := class<abstract>:
    Eval():t
    Pick(?Alt:?t = false, ?More:[]t = array{}, ?Tag:[int]t = map{}, ?N:int = 0):t =
        if (A := Alt?) then A else Eval()
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
    Pick<override>(?Alt:?int = false, ?More:[]int = array{}, ?Tag:[int]int = map{}, ?N:int = 0):int =
        if (A := Alt?) then A + N else V + More.Length + N
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    A:a
    B:b
    Eval<override>():tuple(a, b) = (A, B)
    Pick<override>(?Alt:?tuple(a, b) = false, ?More:[]tuple(a, b) = array{}, ?Tag:[int]tuple(a, b) = map{}, ?N:int = 0):tuple(a, b) =
        if (X := Alt?) then X
        else if (Y := More[N]) then Y
        else if (Z := Tag[N]) then Z
        else (A, B)
hidE(a:type) := class(expr(int)):
    H:a
    K:int
    Eval<override>():int = K
    Pick<override>(?Alt:?int = false, ?More:[]int = array{}, ?Tag:[int]int = map{}, ?N:int = 0):int =
        if (A := Alt?) then A else K * 10 + More.Length + N
Run0(E:expr(t) where t:type):t = E.Pick()
Run1(E:expr(t), X:t where t:type):t = E.Pick(?Alt := option{X})
Run2(E:expr(t), X:t where t:type):t = E.Pick(?More := array{X}, ?N := 0)
Run3(E:expr(t), X:t where t:type):t = E.Pick(?N := 1, ?Tag := map{1 => X})
Main():void =
    P := pairE(int, string){A := 1, B := "b"}
    Print("{Run0(P)(1)} {Run1(P, (2, "c"))(1)} {Run2(P, (3, "d"))(1)} {Run3(P, (4, "e"))(1)}")
    L := lit{V := 5}
    Print("{Run0(L)} {Run1(L, 6)} {Run2(L, 7)} {Run3(L, 8)}")
    H := hidE(string){H := "h", K := 9}
    Print("{Run0(H)} {Run1(H, 10)} {Run2(H, 11)} {Run3(H, 12)}")
    E:expr(tuple(int, string)) = P
    Print("{E.Pick()(1)} {E.Pick(?N := 2)(0)}")
