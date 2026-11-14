# expect: 3:21: expected ',', ';', a new line or '}' after a member, found 'block'
# Two members of a class in braces on one line need a separator (Book of Verse tests, ClassBlockClause.versetest:19).
c := class{X:int = 1 block{}}
Main():void = {}
