# Imported by ../modules.verse; it imports a file of its own.
using{"shapes_base"}
square := class(shape):
    Side:int
    Area<override>():int = Side * Side
Area(S:shape):int = S.Area()
