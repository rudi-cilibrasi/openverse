# Interface methods implemented by two classes, a default implementation in
# the interface, and dispatch through an array of the interface.
# Tests LANGUAGE.md, Supported, Classes: "class(parent, interface, ...)",
# "interface"; Classes: "the nearest in its class chain, else the default of
# the interface that declares the method".
# OpenVerse prints (Lean and C agree):
#   0 quiet 1 | 1 LOUD 9 | 2 quiet 1
speaker := interface:
    Speak()<computes>:string
    Volume()<computes>:int = 1

loud_cls := class(speaker):
    Speak<override>()<computes>:string = "LOUD"
    Volume<override>()<computes>:int = 9

quiet_cls := class(speaker):
    Speak<override>()<computes>:string = "quiet"

Main():void =
    All:[]speaker = array{quiet_cls{}, loud_cls{}, quiet_cls{}}
    for (I -> S : All):
        Print("OVPROBE {I} {S.Speak()} {S.Volume()}")
