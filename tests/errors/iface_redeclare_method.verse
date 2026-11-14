# expect: F of interface I1 is inherited from I0: an interface declares no inherited member again
# An interface declares no inherited method again, with a body or without
I0 := interface:
    F():int = 1
I1 := interface(I0):
    F():int = 2
c := class(I1) {}
Main():void = Print("{c{}.F()}")
