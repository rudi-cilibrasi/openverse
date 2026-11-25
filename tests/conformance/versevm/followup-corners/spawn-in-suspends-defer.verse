# followup-corners (#724): A spawn in a defer of a <suspends> function (UEFN
# admits and runs one in a function that does not suspend, followup-
# refused/spawn-in-defer): admitted, and when does the spawned task start
# and end?
# OpenVerse (Lean and C agreeing): refused, spawn in a defer of a <suspends>
# function is not supported (#156); a defer of a function that cannot
# suspend may spawn.
# If Epic refuses it, OpenVerse agrees on the verdict. If it admits it, its
# lines say what OpenVerse should do: run body done | side start | defer end
# | after run | side done | after wait is the spawned task started inside
# the defer, running to its first Sleep, and outliving the function.
# Not yet compiled or run by UEFN.
Side()<suspends>:void =
    Print("OVPROBE side start")
    Sleep(0.1)
    Print("OVPROBE side done")

Run()<suspends>:void =
    defer:
        spawn{Side()}
        Print("OVPROBE defer end")
    Sleep(0.1)
    Print("OVPROBE run body done")

Main()<suspends>:void =
    Run()
    Print("OVPROBE after run")
    Sleep(0.3)
    Print("OVPROBE after wait")
