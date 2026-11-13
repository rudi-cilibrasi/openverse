# expect: <scoped{M1}> on Field<override>: an override has the access of the member it overrides
# (AccessLevelInheritance.versetest:229: "Can't narrow scope", error 3650)
Scoped_M1 := scoped{M1}
M1<public> := module:
    Base<public> := class:
        Field<Scoped_M1>:int = 42
    Child<public> := class(Base):
        Field<override><Scoped_M1>:int = 50
Main():void = {}
