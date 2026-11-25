# Control of join-generic-effects-decides: a generic function, Identity
# <computes>, as a value of type{_(:int)<computes><decides>:int}, no join.
# Book: Tests/Function.versetest:217 (valid on both VMs). OpenVerse prints
#   value 1
# A refusal here means generic functions are no values in UEFN 43.12 (the
# Book's types-other refusals count 4 such cases).
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-19) admits it, and its Verse VM prints value 1, as OpenVerse does.
Identity(X:t where t:type)<computes>:t = X

Apply()<computes><decides>:int =
    F:type{_(:int)<computes><decides>:int} = Identity
    F[1]

Main():void =
    if (V := Apply[]):
        Print("OVPROBE value {V}")
