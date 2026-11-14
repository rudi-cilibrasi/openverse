# expect: 5:33: the parameter C of a <localizes> message is a c, which a message does not render
# A message's parameter is an int, a float, a string or a message: every
# parameter is rendered, used or not (Book of Verse tests, Localization.versetest:113, 3509).
c := class{}
BadMsg<localizes>(C:c):message = "The Message"
Main():void = {}
