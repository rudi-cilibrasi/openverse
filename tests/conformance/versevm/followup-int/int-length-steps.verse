# Follow-up (#724): where repeated squaring stops. int-length-max and
# int-length-over gave no output on the Verse VM (three sessions each), and
# neither did this probe without the Sleep: output seems to be delivered
# when the task yields. After step K the value is 2^(2^K).
# OpenVerse prints "step 1" to "step 19", then the overflow error at step 20.
Main()<suspends>:void =
    var H:int = 2
    for (K := 1..20):
        set H *= H
        Print("OVPROBE step {K}")
        Sleep(0.0)
