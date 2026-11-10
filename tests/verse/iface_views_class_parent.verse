# A class with a class parent that lists an interface at type arguments
# that are not a prefix of its own (q's are p's u, then its t; container
# gets t): references to container go through views (#351), and q has
# hidden fields for all of its type parameters, which a dispatch through a
# view reads (the program is elaborated again with them); also below q,
# through generic code, with a <suspends> method and a cast back down
container(t:type) := interface:
    Get():t
    Wait(X:t)<suspends>:t
sink(u:type) := interface:
    Put(X:u):int
p(t:type) := class(sink(t)):
    Put<override>(X:t):int = 1
q(u:type, t:type) := class(p(u), container(t)):
    V:t
    Get<override>():t = V
    Wait<override>(X:t)<suspends>:t =
        Sleep(0.0)
        X
    Put<override>(X:u):int = 2
r(t:type) := class(q(string, []t)):
    Put<override>(X:string):int = 3
GC(C:container(x) where x:type):x = C.Get()
GW(C:container(x), V:x where x:type)<suspends>:x = C.Wait(V)
Main()<suspends>:void =
    C:container(string) = q(int, string){V := "v"}
    Print(C.Get())
    Cs:[]container(float) = array{q(char, float){V := 1.5}, q(string, float){V := 2.5}}
    for (X : Cs) { Print("{X.Get()} {GC(X)} {GW(X, 3.5)}") }
    Ss:[]sink(int) = array{p(int){}, q(int, char){V := 'c'}}
    for (S : Ss) { Print("{S.Put(1)}") }
    Ds:[]container([]int) = array{q(char, []int){V := array{1}}, r(int){V := array{2, 3}}}
    for (D : Ds):
        if (R := r[D]) then Print("r {R.V.Length} {R.Put("s")}") else Print("not r {D.Get().Length}")
