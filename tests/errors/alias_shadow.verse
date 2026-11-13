# expect: 4:4: 'id' is already defined (as a type alias); Verse does not allow shadowing
id := int
Main():void =
    id := 1
    Print("{id}")
