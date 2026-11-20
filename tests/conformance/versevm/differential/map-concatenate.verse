# ConcatenateMaps: the values and the order when both maps have a key.
# Tests LANGUAGE.md, Maps: "ConcatenateMaps(M1, M2) (exactly two maps ...;
# their pairs laid down in turn, as map{...} lays its own: a key both maps
# have takes the second map's value at the second map's place, the Book's
# API reference and ConcatenateMaps.versetest 21, 33)". The other reading
# (the first map's place): 1a,2X,3c,4d.
# OpenVerse prints (Lean and C agree):
#   ab 1a,3c,2X,4d | ba 4d,1a,2b,3c | empty 2X,4d 1a,2b,3c
Keys(M:[int]string):string = Join(for (K -> V : M) { "{K}{V}" }, ",")

Main():void =
    A:[int]string = map{1 => "a", 2 => "b", 3 => "c"}
    B:[int]string = map{2 => "X", 4 => "d"}
    Print("OVPROBE ab {Keys(ConcatenateMaps(A, B))}")
    Print("OVPROBE ba {Keys(ConcatenateMaps(B, A))}")
    E:[int]string = map{}
    Print("OVPROBE empty {Keys(ConcatenateMaps(E, B))} {Keys(ConcatenateMaps(A, E))}")
