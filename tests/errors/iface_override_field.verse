# expect: <override> on V of interface I1: an interface overrides nothing
# Nor a field a new value or a narrower type (the Book's tests,
# InterfaceWithFields.versetest: "Can't override in an interface")
C0 := class{}
C1 := class(C0){}
I0 := interface {V:C0=C0{}}
I1 := interface(I0) {V<override>:C1=C1{}}
Main():void = {}
