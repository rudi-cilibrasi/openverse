# expect: save is <persistable>, so its field 'Mode' must persist, and mode does not
# (Book of Verse ch. 17: "Enums without <persistable> specifier cannot be
# used" in a persistable struct; the Book's persistable.versetest:59)
mode := enum:
    On
    Off
save := struct<persistable>:
    Score:int = 0
    Mode:mode = mode.Off
Main():void = {}
