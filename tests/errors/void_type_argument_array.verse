# expect: expected []tuple(), found []int (in a call of box.Put)
# (Book of Verse ch. 2, "Conversion is one-way": "A type parameter bound to
# []void is invariant, though, so only []void (or []true) fits there";
# Void.versetest:260)
box(t:type) := class:
    Put(:t):void = {}
Main():void =
    Y:[]int = array{1}
    box([]void){}.Put(Y)
