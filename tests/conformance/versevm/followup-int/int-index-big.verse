# Follow-up (#724): an index beyond 64 bits. OpenVerse fails, as for any
# index out of range, and prints "index failed", "negative index failed",
# "set failed"; a runtime error would stop the session.
Next(N:int)<computes>:int = N + 1

Main():void =
    Big := Next(9223372036854775807)
    A := array{10, 20, 30}
    if (A[Big]) then Print("OVPROBE index succeeded") else Print("OVPROBE index failed")
    if (A[-Big - 1]) then Print("OVPROBE negative index succeeded") else Print("OVPROBE negative index failed")
    var B:[]int = array{1, 2}
    if (set B[Big] = 3) then Print("OVPROBE set succeeded") else Print("OVPROBE set failed")
