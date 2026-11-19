# expect: 11:4: mod.child inherits <concrete> from mod.base, so its field 'valueChild' needs a default (Epic's Verse compiler, UEFN 43.12: error 3519)
# a class below a <concrete> class is concrete too: every field it has
# needs a default. UEFN 43.12 (++Fortnite+Release-43.12-CL-60598086)
# refuses this with error 3519, "Data member `valueChild` of class `child`
# must have an initializer. (Reason: inherited class 'base' is `concrete`)",
# as the Book of Verse's tests do (SOL-3366-MakeClassesConcreteByDefault.versetest:8;
# tests/conformance/versevm/book/book-concrete-inherited.verse)
mod := module:
    base := class<concrete>:
        valueBase:int = 42
    child := class(base):
        valueChild:int
Main():void =
    Print("compiled")
