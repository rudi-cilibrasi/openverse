# Types as values in a struct's fields (Book of Verse ch. 11, "Metatypes"):
# a field of type subtype(c) or type, and a class named as a value in its
# default, as a class's field has them.
base := class:
    Id:int = 0
anchor := class(base) {}
plain := class(base) {}
kinds := struct:
    Kind:subtype(base) = anchor
    Any:type = plain
Name(K:subtype(base), X:base)<computes>:string = if (K[X]) then "yes" else "no"
Main():void =
    K := kinds{}
    Print(Name(K.Kind, anchor{}))
    Print(Name(K.Kind, plain{}))
    Print(Name(kinds{Kind := plain}.Kind, plain{}))
