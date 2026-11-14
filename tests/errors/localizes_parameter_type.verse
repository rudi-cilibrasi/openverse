# expect: 5:33: no overload of $localizeValue takes (c)
# A message's parameter is an int, a float, a string or a message: every
# parameter is rendered, used or not (Book of Verse tests, Localization.versetest:113, 3509).
c := class{}
BadMsg<localizes>(C:c):message = "The Message"
Main():void = {}
