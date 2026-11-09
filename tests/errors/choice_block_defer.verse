# expect: 3:42: a choice (a | b) cannot be lifted from here
Main()<transacts>:void =
    for (X := block{ defer: Print("d"); 1 | 2 }):
        Print("{X}")
