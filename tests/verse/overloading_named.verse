# overloads with named parameters (Book of Verse ch. 6): told apart by the
# named arguments a call gives, in any order

Process(X:int):string = "one parameter"
Process(X:int, ?Option:string):string = "two parameters ({Option})"

Draw(?Width:int, ?Height:int):string = "rect {Width}x{Height}"
Draw(?Radius:int):string = "circle {Radius}"

Label(X:int, ?Prefix:string = "#"):string = "{Prefix}{X}"
Label(S:string):string = "s:{S}"

Main():void =
    Print(Process(42))
    Print(Process(42, ?Option := "test"))
    Print(Draw(?Width := 2, ?Height := 3))
    Print(Draw(?Height := 3, ?Width := 2))
    Print(Draw(?Radius := 5))
    Print(Label(7))
    Print(Label(7, ?Prefix := "n"))
    Print(Label("x"))
