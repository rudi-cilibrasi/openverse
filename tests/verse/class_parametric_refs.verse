# Parametric classes are references (#39): objects with var fields, shared
# by every variable that refers to them, compared by identity when
# <unique>, and recursive through their own type, at every instantiation.

stack(t:type) := class:
    var Items:[]t = array{}
    Push(X:t):void = set Items += array{X}
    Pop()<decides>:t =
        X := Items[Items.Length - 1]
        set Items = for (I -> Y : Items, I < Items.Length - 1) { Y }
        X
    Size():int = Items.Length

# a generic linked list
node(t:type) := class:
    Value:t
    var Next:?node(t) = false

Cons(X:t, L:?node(t) where t:type):?node(t) = option{node(t){Value := X, Next := L}}

Length(L:?node(t) where t:type):int =
    if (N := L?) then 1 + Length(N.Next) else 0

# reverse a list in place, by rewriting its links
Reverse(L:?node(t) where t:type):?node(t) =
    var Prev:?node(t) = false
    var Cur:?node(t) = L
    loop:
        if (N := Cur?):
            Next := N.Next
            set N.Next = Prev
            set Prev = option{N}
            set Cur = Next
        else:
            break
    Prev

Show(L:?node(int)):string =
    if (N := L?) then "{N.Value} {Show(N.Next)}" else "."

cell(t:type) := class:
    var Value:t

Swap(A:cell(t), B:cell(t) where t:type):void =
    X := A.Value
    set A.Value = B.Value
    set B.Value = X

token(t:type) := class<unique>:
    Payload:t

Main():void =
    S := stack(int){}
    T := S
    S.Push(1)
    S.Push(2)
    T.Push(3)
    Print("{S.Size()} {T.Size()}")
    if (X := S.Pop[]) then Print("popped {X}, {T.Size()} left")
    Words := stack(string){}
    Words.Push("hello")
    if (W := Words.Pop[]) then Print(W)
    if (not Words.Pop[]) then Print("empty")
    L := Cons(1, Cons(2, Cons(3, false)))
    Print("{Length(L)}: {Show(L)}")
    R := Reverse(L)
    Print("{Length(R)}: {Show(R)}")
    # the old head is now the last node
    Print("{Length(L)}: {Show(L)}")
    Ls := Cons("a", Cons("b", false))
    Print("{Length(Reverse(Ls))}")
    A := cell(int){Value := 1}
    B := cell(int){Value := 2}
    Swap(A, B)
    Print("{A.Value} {B.Value}")
    P := cell(string){Value := "p"}
    Q := cell(string){Value := "q"}
    Swap(P, Q)
    Print("{P.Value}{Q.Value}")
    K1 := token(string){Payload := "k"}
    K2 := token(string){Payload := "k"}
    if (K1 = K1) then Print("a token is itself")
    if (not (K1 = K2)) then Print("two tokens differ, with equal payloads")
