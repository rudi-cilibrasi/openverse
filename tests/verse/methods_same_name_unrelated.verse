# unrelated classes with methods of one name and different lists are not overloads (#106 review)
i1 := interface:
    M():string
i2 := interface:
    M():string
c := class(i1, i2):
    (i1:)M<override>():string = "one"
    (i2:)M<override>():string = "two"
other := class:
    M(S:string):string = S
Main():void =
    X := c{}
    Print(X.(i1:)M())
    Print(X.(i2:)M())
    Print(other{}.M("z"))
