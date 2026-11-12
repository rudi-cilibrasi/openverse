# Fields of interfaces referred to through views (#351), as the review found
# them: a read or set tests only the classes whose view can be the
# reference's (c gives i2 string, d int; ifix gives sink int), and is typed
# when none can; a variable of an interface whose class has a field from one
# seen through views (ib, which c gives its second) starts with that field
# at the type c gives it
i1(t:type) := interface:
    A():t
i2(t:type) := interface:
    var Note:t
    B():t
c := class(i1(int), i2(string)):
    A<override>():int = 7
    B<override>():string = Note
d := class(i1(string), i2(int)):
    A<override>():string = "a"
    B<override>():int = Note
container(t:type) := interface:
    Get():t
sink(u:type) := interface:
    var Count:int = 0
    Put(X:u):int
both(t:type, u:type) := class(container(t), sink(u)):
    V:t
    Get<override>():t = V
    Put<override>(X:u):int = Count
ifix := class(sink(int)):
    Put<override>(X:int):int = 2
ia(t:type, u:type) := interface:
    A2():int
ib(u:type) := interface:
    var Q:u
e(t:type, u:type) := class(ia(t, u), ib(u)):
    A2<override>():int = 1
Sum(Is:[]i2(int)):int =
    var S:int = 0
    for (I : Is) { set S += I.Note }
    S
Main():void =
    I:i2(string) = c{Note := "n"}
    set I.Note = "m"
    Print("{I.B()} {I.Note}")
    J:i2(int) = d{Note := 4}
    Print("{J.B()} {J.Note} {Sum(array{J, d{Note := 5}})}")
    S:sink(string) = both(int, string){V := 1}
    set S.Count = 3
    Print("{S.Count} {S.Put("a")}")
    X:ia(int, string) = e(int, string){Q := "q"}
    Print("{X.A2()}")
