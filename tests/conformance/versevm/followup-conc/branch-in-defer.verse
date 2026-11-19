# A branch in a defer block. OpenVerse refuses it ("branch in a defer is not
# supported (#156)"). Does Epic's compiler admit it? If it does, the branch's
# parent would be the task that runs the defer (here Main's code, through the
# function's exit): it would print
#   function returned | deferred branch done | after wait
Exit()<suspends>:void =
    defer:
        branch:
            Sleep(0.1)
            Print("OVPROBE deferred branch done")
    Sleep(0.05)

Main()<suspends>:void =
    Exit()
    Print("OVPROBE function returned")
    Sleep(0.3)
    Print("OVPROBE after wait")
