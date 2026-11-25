# Control of interface-fn-param-generic: the same parametric interface and
# class with a method F(X:t), no function parameter. Not a Book case.
# OpenVerse prints
#   called
# A refusal here means parametric interfaces themselves are refused.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-19) admits it, and its Verse VM prints called, as OpenVerse does.
a(t:type) := interface:
    F(X:t)<transacts>:void

b := class(a(int)):
    F<override>(X:int)<transacts>:void = {}

Main():void =
    Obj:b = b{}
    Obj.F(1)
    Print("OVPROBE called")
