# An interface may be inherited again through another parent (Book of Verse
# tests, Interface.versetest:34-41), once: a diamond, and an interface above
# a class's parent named again.
t1 := interface { Get():int }
t2 := interface(t1) {}
t3 := interface(t1) {}
c0 := class(t1, t2) { Get<override>():int = 1 }
c1 := class(t2, t3) { Get<override>():int = 2 }
c2 := class(c0, t1) { Get<override>():int = 3 }
Show(X:t1):void = Print("{X.Get()}")
Main():void =
    Show(c0{})
    Show(c1{})
    Show(c2{})
