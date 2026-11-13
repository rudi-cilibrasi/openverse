# A `;` may end a line: the next item follows the line rules, so a class's
# last field ending in `;` does not take the next definition into the class
# (Book of Verse tests: `DataMemberX<final>: int = 0;`).
class_x := class:
    A<final>: int = 0;
    B:int = 2;
point := struct:
    X:int = 3;
F():int =
    Y := 1;
    Y + 4;
Main():void =
    Print("{class_x{}.B} {point{}.X} {F()}")
