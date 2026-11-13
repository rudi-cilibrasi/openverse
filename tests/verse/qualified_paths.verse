# A path qualifier: openverse stands in for /Verse.org/Verse with its
# built-in types (Book of Verse ch. 16: `int` is `(/Verse.org/Verse:)int`).
Twice(X:(/Verse.org/Verse:)int):(/Verse.org/Verse:)int = 2 * X
Name:(/Verse.org/Verse:)string = "path"
Main():void =
    Values:[](/Verse.org/Verse:)float = array{1.5, 2.5}
    Print("{Twice(21)} {Name} {Values.Length}")
