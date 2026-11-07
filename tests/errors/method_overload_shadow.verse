# expect: 'M' is already a field or method of c
c := class:
    M(X:int):string = "i"
    M(S:string):string = "s"
    N():string =
        M := 5
        "{M}"
Main():void = Print(c{}.N())
