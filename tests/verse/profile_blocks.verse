# profile(Tag): body, profile: body, profile{body}: the body's value, the
# tag a string (Book of Verse ch. 7, "Profiling"); openverse measures nothing
s:?string = option{"123"}
F()<decides>:int =
    profile(s?):
        1+1
G():int =
    X := profile("Damage"):
        3 * 4
    Y := profile { X + 1 }
    Z := profile:
        Y * 2
    Z
Main():void =
    if (A := F[]) then Print("{A} {G()}")
