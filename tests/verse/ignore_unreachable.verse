# @ignore_unreachable on a return or a break: the code after it, never
# reached, is no warning (Book of Verse tests, Reachability.versetest:94,
# SemicolonsVsCommas.versetest:97, Enum.versetest:540); without it, it is
F(X:int):void = F(@ignore_unreachable return)
G(X:int):void = G(return)
e := enum{A, B}
Name(X:e):int =
    case (X):
        e.A => 1
        e.B => 2
        @ignore_unreachable _ => 3
Main():void =
    loop:
        1
        @ignore_unreachable break
    Print("{Name(e.A)} {Name(e.B)}")
