# A module's items are the lines indented more than the line of its
# `module:`, each at a column of its own (Book of Verse tests,
# Modules/Module.versetest:167, Attributes/AccessLevelInheritance.versetest:605)
A := module:
     F<public>():int = 1
    G<public>():int = A.F() + 1
   M<public> := module:
        H<public>():int = 10
   K<public>():int = M.H() + G()
Main():void = Print("{A.F()} {A.G()} {A.K()}")
