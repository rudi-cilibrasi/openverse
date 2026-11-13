# var<w> X<r>: the write access is at least as restrictive as the read access (Book of Verse
# ch. 12), judged with what the field is in: in an internal class, both reach the same code.
gauge := class:
    var<public> Level<internal>:int = 0
    var<protected> Peak<internal>:int = 0
Main():void =
    G := gauge{}
    set G.Level = 3
    Print("{G.Level} {G.Peak}")
