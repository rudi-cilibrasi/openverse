# expect: 3:0: expected int, found tuple(int, int)
# A braced body whose statements a comma joins is a tuple, not its last value (SemicolonsVsCommas.versetest:28)
F():int = {0, 1}
Main():void = Print("{F()}")
