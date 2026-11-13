# expect: openverse has no module at the path /Verse.org/VerseTests/c
c := class:
    var V:int = 0
    block:
        set (/Verse.org/VerseTests/c:)V = 1
Main():void = {}
