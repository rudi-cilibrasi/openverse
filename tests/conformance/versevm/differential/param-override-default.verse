# A method's named parameter with a default overridden in a subclass with
# another default: which default a call through the parent's type uses.
# Tests LANGUAGE.md, Functions: "a call dispatched to an override evaluates
# that override's own default for an omitted argument". The other reading
# (the static type's default) would print 1 for the second call.
# OpenVerse prints (Lean and C agree):
#   1 200 200 300
base_dflt := class:
    Pick(?N:int = 1)<computes>:int = N

sub_dflt := class(base_dflt):
    Pick<override>(?N:int = 2)<computes>:int = N * 100

Main():void =
    B:base_dflt = base_dflt{}
    S:base_dflt = sub_dflt{}
    D:sub_dflt = sub_dflt{}
    Print("OVPROBE {B.Pick()} {S.Pick()} {D.Pick()} {S.Pick(?N := 3)}")
