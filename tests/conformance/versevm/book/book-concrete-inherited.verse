# Book: Tests/Bugs/SOL-3366-MakeClassesConcreteByDefault.versetest:8 refuses
# (3519) a field without a default in a subclass of a <concrete> class.
mod := module:
    base := class<concrete>:
        valueBase:int = 42
    child := class(base):
        valueChild:int

Main():void =
    Print("OVPROBE compiled")
