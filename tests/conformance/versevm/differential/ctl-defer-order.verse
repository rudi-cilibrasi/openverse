# defer: several in one block run last registered first, at the block's end,
# after its value is computed; a nested block's defers run when it ends.
# Tests LANGUAGE.md, defer: "runs that block when its scope exits (Book of
# Verse ch. 7): at the scope's end, after its value is computed ... Several
# run last registered first".
# OpenVerse prints (Lean and C agree):
#   inner body | inner defer | outer body | compute result | defer two
#   defer one | returned 42
Value(S:string, V:int):int =
    Print("OVPROBE compute {S}")
    V

Work():int =
    defer:
        Print("OVPROBE defer one")
    defer:
        Print("OVPROBE defer two")
    block:
        defer:
            Print("OVPROBE inner defer")
        Print("OVPROBE inner body")
    Print("OVPROBE outer body")
    Value("result", 42)

Main():void =
    R := Work()
    Print("OVPROBE returned {R}")
