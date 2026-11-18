# Control for book-concrete-inherited: the same classes with a default for
# the subclass's field (Tests/Bugs/SOL-3366-MakeClassesConcreteByDefault.versetest:3
# accepts the <concrete> base alone).
mod := module:
    base := class<concrete>:
        valueBase:int = 42
    child := class(base):
        valueChild:int = 0

Main():void =
    Print("OVPROBE compiled")
