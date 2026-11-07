# Classes, phase 1 (#14; Book of Verse ch. 10): fields and methods, Self,
# parametric classes. Without var fields a class is a tuple in Verse Core, and
# a method of class c is a function c.M whose first parameter is Self.

counter := class:
    Name:string
    Step:int = 1
    # fields by bare name
    Next(X:int):int = X + Step
    # methods by bare name
    Twice(X:int):int = Next(Next(X))
    Rename(N:string):counter = counter{Name := N, Step := Step}
    Me():counter = Self
    Describe():string = "{Name} steps by {Step}"
    # a <decides> method is called with []
    Below(X:int)<decides>:int =
        X < 10
        Next(X)

box(t:type) := class:
    Value:t
    Get():t = Value
    # a method with its own type parameter
    Pair(Other:u where u:type):tuple(t, u) = (Value, Other)
    Wrap():box(box(t)) = box(box(t)){Value := Self}

stack(t:type) := class:
    Items:[]t = array{}
    Push(X:t):stack(t) = stack(t){Items := Items + array{X}}
    Peek()<decides>:t = Items[Items.Length - 1]
    Size():int = Items.Length

# a field default is elaborated where it is defined, not in the method that
# constructs the struct (whose class has a field of the same name)
Limit:int = 10
config := struct:
    Max:int = Limit

widget := class:
    Limit:int = 99
    Make():config = config{}

record := struct:
    Pair:tuple(int, string)

# classes in generic code
Fill(S:stack(t), X:t, N:int where t:type):stack(t) =
    if (N <= 0) then S else Fill(S.Push(X), X, N - 1)

Main():void =
    C := counter{Name := "c", Step := 3}
    Print("{C.Next(1)} {C.Twice(1)} {C.Describe()}")
    D := C.Rename("d")
    Print(D.Me().Describe())
    if (V := C.Below[4]) then Print("below: {V}")
    if (not C.Below[40]) then Print("40 is not below")
    B := box(int){Value := 7}
    P := B.Pair("seven")
    Print("{B.Get()} {P(1)} {B.Wrap().Get().Get()}")
    S := Fill(stack(string){}, "x", 3).Push("top")
    if (T := S.Peek[]) then Print("{S.Size()} items, top {T}")
    Empty := stack(int){}
    if (not Empty.Peek[]) then Print("empty stack")
    # arrays and options of classes
    Cs := array{counter{Name := "a"}, counter{Name := "b", Step := 2}}
    for (X : Cs) { Print(X.Describe()) }
    O:?counter = option{C}
    if (Y := O?) then Print("option holds {Y.Name}")
    # a field indexed directly: S.Items[i] (a class) and R.Pair(1) (a struct)
    if (First := S.Items[0]) then Print("first {First}")
    R := record{Pair := (1, "one")}
    Print(R.Pair(1))
    Print("config max {widget{}.Make().Max}")
    # receivers are evaluated once, before the arguments
    Print("{counter{Name := "e"}.Rename("f").Twice(0)}")
