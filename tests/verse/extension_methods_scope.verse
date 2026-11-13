# Extension methods are scoped like functions (Book of Verse ch. 6): found
# from the call's module outward and in the modules it opens, <public> ones
# from outside; a class's own are methods of Self (a closure over its
# fields); a type's own member of the name is the call's unless only the
# extension method takes it

Utils := module:
    (S:string).Shout<public>():string = "{S}!"
    (S:string).Whisper():string = "{S}..."
    # (internal: used inside the module)
    Quiet<public>(S:string):string = S.Whisper()
    Inner<public> := module:
        (N:int).Squared<public>():int = N * N
    UseInner<public>():int = 3.Squared()

using { Utils }
using { Utils.Inner }

# a class's own extension method reads the class's fields
game_manager := class:
    Multiplier:int = 10
    (Score:int).Scaled()<computes>:int = Score * Multiplier
    Process(Value:int)<computes>:int = Value.Scaled()

# an extension method of a class, called from a method of a class below it,
# with Self as the receiver, written or not
base := class:
    X:int
(B:base).Describe():string = "base {B.X}"
derived := class(base):
    Written():string = Self.Describe()
    Bare():string = Describe()

# a bare call that the extension method does not take keeps its meaning
(I:int).Twice():int = 2 * I
Twice():int = 7
counter := class:
    Get():int = Twice()

# a member of the receiver's type, and an extension method of one name on
# another type: each where it applies
shape := class:
    Area():int = 6
(I:int).Area():int = I * I

# a method and an extension method of one name that a call tells apart
box := class:
    Put(I:int):string = "method {I}"
(B:box).Put(S:string):string = "extension {S}"

Main():void =
    Print("Hello".Shout())
    Print(Quiet("psst"))
    Print("{4.Squared()} {UseInner()}")
    Print("{game_manager{}.Process(5)}")
    D := derived{X := 2}
    Print("{D.Written()} / {D.Bare()} / {D.Describe()}")
    Print("{counter{}.Get()} {3.Twice()}")
    Print("{shape{}.Area()} {3.Area()}")
    Print("{box{}.Put(1)} / {box{}.Put("a")}")
