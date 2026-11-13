# (#283) a function with several values inlined in one whose parameter has
# the name of a definition its body uses: the parameter is (local:)K (Book of
# Verse ch. 16), named so that no inlined use of the global K meets it (this
# was tests/errors/multi_capture.verse, refused for the capture, before the
# Book's rule refused the unqualified parameter)
K:int = 5
F():int = K | K + 1
H((local:)K:int):int = if (V := F()) then V + (local:)K - 100 else 0
Main():void = Print("{H(100)}")
