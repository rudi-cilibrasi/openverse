# expect: Health of entity is <protected>: only entity and the classes below it may use it
# (Book of Verse ch. 12, "Protected"; Classes/AccessSpecifiers.versetest:109)
entity := class:
    var Health<protected>:int = 100
Read(E:entity):int = E.Health
Main():void = Print("{Read(entity{})}")
