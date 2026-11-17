# expect: 3:19: a return in a <decides> function must be in tail position (the last expression of its body, or a branch of one), as its body is a failure context (the Book of Verse's tests, Return.versetest:157)
F(X:int)<decides>:int=
    Y:=if(X>2)then(return 0)else X
    Y|Y+1
Main():void=if(V:=F[3])then Print("{V}")
