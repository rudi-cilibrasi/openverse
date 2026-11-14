# expect: requires convergence
Helper()<computes>:int=42
# (in option{}: a field's default cannot fail, Book of Verse ch. 13)
c:=class<computes>{Value:?int=option{first{Helper()|1}}}
Main():void={}
