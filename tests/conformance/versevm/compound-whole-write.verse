Replacement()<computes>:[]int = array{42}

Main()<transacts>:void =
    var Row:[]int = array{1, 2, 3}
    if (set Row += (if (set Row = array{0}; 0 = 0)
        then Replacement() else Replacement()), 0 = 0):
        Print("OVPROBE length {Row.Length}")
        if (First := Row[0]):
            Print("OVPROBE first {First}")
        if (Second := Row[1]):
            Print("OVPROBE second {Second}")
    else:
        Print("OVPROBE update failed")
