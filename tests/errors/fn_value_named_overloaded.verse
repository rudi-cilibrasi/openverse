# expect: Process is overloaded: an overloaded function cannot be used as a value
# Named parameters do not lift the Book capture rule (ch. 6, "Capture", #503)
Process(Value:int):string = "one"
Process(Value:int, ?Option:string):string = "two"
Main():void =
    F:type{_(:int, ?Option:string):string} = Process
    Print(F(1, ?Option := "x"))
