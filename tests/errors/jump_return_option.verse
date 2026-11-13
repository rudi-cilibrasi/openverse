# expect: 3:23: return cannot leave a failure context
# A return in option{} (Return.versetest:129)
F(X:int):?int = option{return false}
Main():void = if (F(1)?) then Print("y")
