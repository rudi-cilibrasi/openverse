# expect: 6:21: the value of the constant Text calls Name, which might not complete
# A data member's definition calls only converging functions (#724, Epic's
# 3582), also through a string's interpolated call of a string. Refused
# already.
Name()<computes>:string = "s"
Text:string = "a{Name()}"
Main():void = Print(Text)
