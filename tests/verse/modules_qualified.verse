# qualified identifiers (M:)F of module members (#145)
A := module:
    B<public> := module:
        F<public>():int = 2
    G<public>():int = 1
H():int = 5
Main():void = Print("{(A.B:)F()} {(A:)G()}")
