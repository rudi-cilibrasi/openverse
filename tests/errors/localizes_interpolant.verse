# expect: an interpolant of a <localizes> message is a parameter's name or a code point
# Only parameter names and code points go in a message's braces (Book of Verse
# ch. 12; its tests, Localization.versetest:159, 3652).
TheMsg<localizes>(Name:string):message = "The Message to {"print"}"
Main():void = {}
