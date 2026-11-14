# expect: <override> on f of interface TT: an interface overrides nothing
# An interface below another gives none of its methods a new body (the
# Book's tests, Interface.versetest: "Interfaces can not override anything")
T := interface:
    f():int = 42
TT := interface(T):
    f<override>():int = 24
c := class(TT) {}
Main():void = Print("{c{}.f()}")
