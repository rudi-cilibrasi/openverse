# Fields of interfaces referred to through views (#351): read and set
# through each class's accessors, dispatched as a method through a view is
# (a field can sit at another place, and has its type at the class's view,
# in each class); in generic code too, through an interface above, at a
# class below that fixes type arguments, and with defaults
tagged(w:type) := interface:
    var Hits:int = 0
container(t:type) := interface:
    Get():t
sink(u:type) := interface(tagged(u)):
    var Count:int
    Last:?u
    Items:[]u = array{}
    Put(X:u):int
both(t:type, u:type) := class(container(t), sink(u)):
    V:t
    var Count<override>:int = 0
    Last<override>:?u = false
    Get<override>():t = V
    Put<override>(X:u):int =
        set Count += 1
        Count
ib := class(both(int, string)):
    Put<override>(X:string):int =
        set Count += 100
        Count
one(u:type) := class(sink(u)):
    W:int
    var Count<override>:int = 10
    Last<override>:?u = false
    Put<override>(X:u):int = Count
i1(t:type) := interface:
    A():t
i2(t:type) := interface:
    var Note:t
    B():t
c := class(i1(int), i2(string)):
    var Note<override>:string = "c"
    A<override>():int = 7
    B<override>():string = Note
GC(S:sink(x) where x:type):int = S.Count
Bump(S:sink(x) where x:type):void = set S.Count += 1000
FirstItem(S:sink(x), D:x where x:type):x = if (Y := S.Items[0]) then Y else D
Hit(T:tagged(x) where x:type):int =
    set T.Hits += 1
    T.Hits
Main():void =
    Ss:[]sink(string) = array{both(int, string){V := 1, Last := option{"l"}, Items := array{"i"}}, one(string){W := 2}, ib{V := 3}}
    for (S : Ss):
        S.Put("a")
        set S.Count += 5
        L := if (Y := S.Last?) then Y else "none"
        Bump(S)
        Print("{S.Count} {GC(S)} {L} {FirstItem(S, "d")} {Hit(S)} {Hit(S)} {S.Hits}")
    I:i2(string) = c{}
    set I.Note = "n"
    Print("{I.Note} {I.B()}")
