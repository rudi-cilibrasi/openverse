# a class below a <concrete> class whose own fields all have defaults is
# admitted, as UEFN 43.12 admits it
# (tests/conformance/versevm/book/book-concrete-inherited-control.verse), and
# is constructed with none given; an override written without a value of a
# field a class above gives one keeps that default (the Book of Verse's
# tests, Attributes/concrete.versetest:59); a class below a <concrete>
# class's parent is not concrete
mod := module:
    base<public> := class<concrete>:
        valueBase<public>:int = 42
    child<public> := class(base):
        valueChild<public>:int = 0
again := class(mod.child):
    valueChild<override>:int
root := class:
    Name:string
leaf := class<concrete>(root):
    Name<override>:string = "leaf"
other := class(root):
    Extra:int
Main():void =
    C := mod.child{}
    Print("child {C.valueBase} {C.valueChild}")
    O := other{Name := "other", Extra := 3}
    Print("{leaf{}.Name} {O.Name} {O.Extra}")
