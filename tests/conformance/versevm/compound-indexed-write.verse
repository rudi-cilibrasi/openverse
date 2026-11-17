Replacement()<computes>:[]int = array{42}

Main()<transacts>:void =
    var Rows:[][]int = array{array{1, 2, 3}}
    if (set Rows[0] += if (set Rows = array{array{0}}; 0 = 0)
        then Replacement() else Replacement()):
        if (Head := Rows[0]):
            Print("OVPROBE length {Head.Length}")
            if (First := Head[0]):
                Print("OVPROBE first {First}")
    else:
        Print("OVPROBE update failed")
