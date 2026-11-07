# expect: is too large: its Verse Core representation has more than 100000 nodes
d(t:type) := struct:
    A:t
    B:t
Main():void =
    X:?d(d(d(d(d(d(d(d(d(d(d(d(d(d(d(d(d(d(d(d(d(d(d(d(int)))))))))))))))))))))))) = false
