# Attributes (Book of Verse ch. 12, "Annotations and Metadata"): the Book's
# @deprecated, @experimental and @available on every place they may be
# written, custom attributes (classes below `attribute`) where their scopes
# allow, constructed by {…} or by a constructor function, and
# @ignore_unreachable on expressions and case arms. None changes what the
# program does, but @available, which takes a definition out of a program
# at a version it is not available at.
using { /Verse.org/Native }

@deprecated
OldAPI():int = 42

@deprecated{Message := "Use NewAPI instead.", DiscontinuedAtFNVersion := 9999}
@experimental
OlderAPI():int = OldAPI()

@available{MinUploadedAtFNVersion := 0}
NewAPI():int = 43

# versioned out: no program openverse runs is at this version, so the F
# below is the only one
@available{MinUploadedAtFNVersion := 4294967295}
F():int = 1
F():int = 2

@deprecated{Message := false}
Limit:int = 10

@attribscope_class @attribscope_attribclass
category := class<computes>(attribute):
    Name:string = "none"

@attribscope_function
perf := class<computes>(attribute):
    MaxMs:int

@attribscope_data
key := class<computes>(attribute):
    Key:string

@attribscope_enum @attribscope_enumerator
tag_attribute := class<computes>(attribute) {}
tag<constructor>(Text:string)<computes> := tag_attribute{}

@category{Name := "weapons"}
weapon := class:
    @key{Key := "damage"}
    Damage:int = 3

    @perf{MaxMs := 16}
    Fire():int = Damage * 2

@category
@experimental
shield := class(weapon):
    @deprecated
    Fire<override>():int = Damage

@tag("colors")
color := enum:
    @tag("first")
    Red
    @deprecated
    Green
    @available{}
    Blue

@deprecated
point := struct:
    @deprecated{Message := "use Y"}
    X:int = 1
    Y:int = 2

@deprecated{Message := "Use NewModule instead."}
M := module:
    @experimental
    Helper<public>():int = 5

ColorName(C:color):string =
    case (C):
        color.Red => "red"
        color.Green => "green"
        color.Blue => "blue"
        @ignore_unreachable color.Red => "never"

Pick(X:int):int =
    if (X = 0):
        Y:int = (@ignore_unreachable return 100)
    X

Main():void =
    Print("{OldAPI()} {OlderAPI()} {NewAPI()} {F()} {Limit}")
    W:weapon = shield{}
    Print("{weapon{}.Fire()} {W.Fire()} {point{}.X} {M.Helper()}")
    Print("{ColorName(color.Red)} {ColorName(color.Blue)} {Pick(0)} {Pick(7)}")
