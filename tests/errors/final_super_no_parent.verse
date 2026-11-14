# expect: a is <final_super>, so it needs a parent: it is the final super class of the class or interface right above it
# (Book of Verse tests, FinalSuperAttribute.versetest:50: "final_super types
# must have some sort of base type", 3679)
a := class<final_super> {}
Main():void = Print("ok")
