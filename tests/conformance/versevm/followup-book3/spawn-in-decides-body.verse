# Edge of the spawn rule (#724): a spawn at the top of a plain <decides>
# function's body, which may call a function without a heap specifier (UEFN
# 43.12 admits followup/decides-body-default-call). OpenVerse admits it (the
# function is only compiled) and prints
#   admitted
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) admits it (compiled only).
Work()<suspends>:void =
    Print("OVPROBE spawned")

Unused()<decides>:void =
    spawn{Work()}

Main():void =
    Print("OVPROBE admitted")
