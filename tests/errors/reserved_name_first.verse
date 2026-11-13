# expect: 'first' is reserved: no definition can take it
# (the Book of Verse's tests reserve it for the future; openverse reads
# first{…} and first(…){…} as macros)
first(X:int):int = X
Main():void = Print("{first(1)}")
