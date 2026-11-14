# An attribute on a qualified definition of a module, (M:)F, is on the
# definition, as it is on F (Book of Verse ch. 12, "Annotations and
# Metadata"; ch. 16): each use of a deprecated one is warned of, a custom
# attribute is checked against the place of what it is on, a function, and
# @available versions out the function it is on.
M := module:
    @attribscope_function
    perf<public> := class<computes>(attribute):
        MaxMs<public>:int

    @deprecated
    (M:)F<public>():int = 1
    @deprecated{Message := "use Y"}
    (M:)X<public>:int = 2
    @deprecated
    (M:)c<public> := class{A<public>:int = 3}
    @deprecated
    (M:)s<public> := struct{B<public>:int = 4}
    @deprecated
    (M:)N<public> := module:
        G<public>():int = 5
    @perf{MaxMs := 16}
    (M:)Fast<public>():int = 6
    @available{MinUploadedAtFNVersion := 4294967295}
    (M:)H<public>():int = 7
    H<public>():int = 8

Main():void =
    Print("{M.F()} {M.X} {M.c{}.A} {M.s{}.B} {M.N.G()} {M.Fast()} {M.H()}")
