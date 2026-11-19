# Control of join-generic-effects-transacts: TransactsIdentity, generic, as
# a value of type{_(:int)<decides><transacts>:int}, no join. Book:
# Tests/Function.versetest:231 (valid on both VMs). OpenVerse prints
#   value 1
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-19) admits it, and its Verse VM prints value 1, as OpenVerse does.
TransactsIdentity(X:t where t:type)<transacts>:t = X

Apply()<transacts><decides>:int =
    F:type{_(:int)<decides><transacts>:int} = TransactsIdentity
    F[1]

Main():void =
    if (V := Apply[]):
        Print("OVPROBE value {V}")
