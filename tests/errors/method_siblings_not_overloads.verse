# expect: Update takes 1 argument(s), found 2
# (siblings below one base, each with its own Update: not overloads, #106 review)
entity := class:
    Id:int = 0
a := class(entity):
    Update(X:int):string = "a"
b := class(entity):
    Update(S:string, N:int):string = "b"
Main():void = Print(a{}.Update(1, 2))
