# expect: using a value of type type{_()<computes>:int} as a value of type type{_()<computes>:rational} is not yet implemented
# (#724: a bound method held by a local is a function value, which converts
# by variance only where it needs no wrapper: int to rational needs one, and
# Epic's Verse compiler refuses it, UEFN 43.12, error 3502,
# followup-coerce2/value-int-rational-result; with --function-coercions it is
# the type error it was, no variance for values)
box(t:type):=class:
    V:t
    Code()<computes>:int=7
Main():void=
    F:=box(string){V:="tag"}.Code
    G:type{_()<computes>:rational}=F
