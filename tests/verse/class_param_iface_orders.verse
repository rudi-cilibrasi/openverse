# parametric classes below a plain interface and a parametric one, in either
# order, and below a parametric interface extending a plain one (#276): the
# root counts its type parameters against the interface with the fewest, so a
# dispatch from the plain interface opens them
shower := interface:
    Show():string
container(t:type) := interface:
    Get():t
sub(t:type) := interface(shower):
    Peek():t
fbox(t:type) := class(shower, container(t)):
    V:t
    Get<override>():t = V
    Show<override>():string = "fbox"
sbox(t:type) := class(container(t), shower):
    V:t
    Show<override>():string =
        X:t = V
        Y:[]t = array{X, Get()}
        "sbox {Y.Length}"
    Get<override>():t = V
pa(t:type, u:type) := class(shower, container(u)):
    A:t
    B:u
    Get<override>():u = B
    Show<override>():string = "pa"
pb(t:type, u:type) := class(container(u), shower):
    A:t
    B:u
    Get<override>():u = B
    Show<override>():string = "pb"
peeker(t:type) := class(sub(t)):
    V:t
    Show<override>():string = "peeker"
    Peek<override>():t = V
Sum(Cs:[]container(int)):int =
    var T:int = 0
    for (C : Cs) { set T += C.Get() }
    T
Main():void =
    Ss:[]shower = array{fbox(int){V := 1}, sbox(string){V := "s"}, pa(logic, int){A := true, B := 2},
                        pb(string, int){A := "a", B := 3}, peeker(int){V := 4}}
    for (S : Ss) { Print(S.Show()) }
    Print("{Sum(array{fbox(int){V := 1}, sbox(int){V := 2}, pa(string, int){A := "x", B := 3}, pb(logic, int){A := false, B := 4}})}")
    Q:sub(int) = peeker(int){V := 5}
    Print("{Q.Peek()} {Q.Show()}")
