# expect: save is <persistable>, so its field 'Owner' must persist, and player does not
# (Book of Verse ch. 17: a struct without <persistable> cannot be a field of one)
player := struct { Name:string = "" }
save := struct<persistable>:
    Score:int = 0
    Owner:player = player{}
Main():void = {}
