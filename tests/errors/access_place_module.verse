# expect: <private> is not allowed on the name of a constant, type or module: a module's definition is <public>, <internal>, <scoped{…}> or <epic_internal>
# (Book of Verse tests, Modules/Module.versetest:36: error 3594)
Shapes<private> := module:
    Sides<public>:int = 4
Main():void = Print("{Shapes.Sides}")
