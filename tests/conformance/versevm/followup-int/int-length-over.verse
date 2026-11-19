# Follow-up (#724): one bit past the longest int by multiplication.
# OpenVerse raises the overflow error at H * H (the session stops after
# "half computed"); without a limit for multiplication Epic would print
# "squared". Epic's Verse VM printed nothing in three sessions, not even
# "half computed", and reported no error; the cause is not known yet.
Main():void =
    var H:int = 2
    for (I := 1..19):
        set H *= H
    Print("OVPROBE half computed")
    S := H * H
    if (S > H) then Print("OVPROBE squared")
