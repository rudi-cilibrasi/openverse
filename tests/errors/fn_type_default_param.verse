# expect: unknown identifier 'Base' (the default of ?A in a function type
# Not even an earlier parameter (#503)
F1(?A:int = 1):int = A
Use(Base:int, F:type{_(?A:int = Base):int}):int = F()
Main():void =
    Print("{Use(1, F1)}")
