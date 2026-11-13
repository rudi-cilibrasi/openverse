# expect: N.square cannot implement M.shape here: implementing M.shape (interface<…>) is internal to M
# (InterfaceAccessVisibility.versetest:9: an interface<internal> is implemented only in its module)
M := module:
    shape<public> := interface<internal>:
        Area<public>():int
N := module:
    square := class(M.shape):
        Area<override>():int = 4
Main():void = {}
