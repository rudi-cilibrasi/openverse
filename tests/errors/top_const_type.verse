# expect: 3:6: a constant at the top level needs its type: write Count:t = …
# A file's top level is a module's scope: a constant there states its type (Book of Verse ch. 16).
Count := 7
Main():void = Print("{Count}")
