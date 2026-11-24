# expect: spawn in a defer of a <suspends> function is not supported
# A defer of a function that cannot suspend may spawn (#724,
# tests/verse/spawn_in_defer); in a <suspends> function it stays refused.
Child()<suspends>:void = Sleep(0.1)
Run()<suspends>:void =
    defer:
        spawn{Child()}
    Sleep(0.0)
Main()<suspends>:void = Run()
