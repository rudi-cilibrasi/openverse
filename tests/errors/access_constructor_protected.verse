# expect: base{…} constructs base here: the constructor of base is <protected>: only base and the classes below it may use it
# (Classes/AccessSpecifiers.versetest:438)
base := class<protected>:
    N:int = 1
Main():void = Print("{base{}.N}")
