# expect: the result of the method box.Make, type{_(:t):void}, has its type parameter t inside a function type
# (#724) a method of a parametric class whose result has the class's type
# parameter inside a function type, called on box(int): the function it
# returns needs a wrapper (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, error 3502, "Using a value of type
# (t->void)->(t->void) as a value of type (int->void)->(int->void)":
# followup-coerce/parametric-method-fn-result).
TakeInt(X:int):void = Print("took {X}")
box(t:type) := class:
    Make(F(:t):void):(t->void) = F
Main():void =
    B := box(int){}
    G := B.Make(TakeInt)
    G(5)
