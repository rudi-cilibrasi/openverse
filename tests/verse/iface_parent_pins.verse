# interfaces that give a parent interface other than their own type parameters
# (#53): c2(t) := interface(container([]t)) has Verse Core type arguments []t, t,
# as a class fixing its parent's would, so a class below it has those first, and
# a dispatch from container(u) to it refines u to []t; a two-parameter pin (kv),
# a chain (c3 through c2), an overriding subclass, <suspends> and spawn
container(t:type) := interface:
    Get():t
    Fetch()<suspends>:t
c2(t:type) := interface(container([]t)):
    Size():int
kv(k:type, v:type) := interface(container(tuple(k, v))):
    Key():k
c3(t:type) := interface(c2(?t)):
    Has():logic
box(t:type) := class(c2(t)):
    Value:t
    Get<override>():[]t = array{Value, Value}
    Fetch<override>()<suspends>:[]t =
        Sleep(0.1)
        array{Value}
    Size<override>():int = 2
bigbox(t:type, w:type) := class(box(t)):
    W:w
    Get<override>():[]t = array{Value, Value, Value}
pair(k:type, v:type) := class(kv(k, v)):
    K:k
    V:v
    Get<override>():tuple(k, v) = (K, V)
    Fetch<override>()<suspends>:tuple(k, v) = (K, V)
    Key<override>():k = K
obox(t:type) := class(c3(t)):
    O:?t
    Get<override>():[]?t = array{O}
    Fetch<override>()<suspends>:[]?t = array{O, O}
    Size<override>():int = 1
    Has<override>():logic = if (O?) then true else false
G(C:container(u) where u:type):u = C.Get()
F(C:container(u) where u:type)<suspends>:u = C.Fetch()
H(C:c2(t) where t:type):int = C.Size() + C.Get().Length
K(C:kv(k, v) where k:type, v:type):tuple(k, v) = (C.Key(), C.Get()(1))
L(C:c3(t) where t:type):int = if (C.Has()?) then C.Size() + 10 else C.Size()
Main()<suspends>:void =
    B := box(int){Value := 3}
    BB := bigbox(int, string){Value := 4, W := "w"}
    Print("{G(B).Length} {H(B)} {G(BB).Length} {H(BB)}")
    P := pair(string, int){K := "k", V := 5}
    Print("{G(P)(0)} {K(P)(1)}")
    O := obox(int){O := option{6}}
    Print("{G(O).Length} {L(O)}")
    Print("{F(B).Length} {F(P)(1)} {F(O).Length}")
    T := spawn{F(BB)}
    Print("{T.Await().Length}")
    Cs:[]container([]int) = array{B, BB}
    Ls := for (C : Cs) { G(C).Length }
    if (A := Ls[0], B2 := Ls[1]) then Print("{A} {B2}")
