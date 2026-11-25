# Control of parametric-interface-var: the parametric interface with a field
# that is not var. Not a Book case. OpenVerse prints
#   defined
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-19) admits it, and its Verse VM prints defined, as OpenVerse does.
i<public>(t:type) := interface:
    Data<public>:t

Main():void =
    Print("OVPROBE defined")
