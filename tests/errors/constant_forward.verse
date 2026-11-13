# expect: the value of the constant First names Second, which is defined after it in the same scope
# A constant may use only one defined before it in its scope (the Book of Verse's tests, DefaultValueAssignment.versetest).
First:int = Second + 1
Second:int = 1
Main():void = Print("{First}")
