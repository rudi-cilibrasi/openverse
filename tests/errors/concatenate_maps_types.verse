# expect: ConcatenateMaps takes maps of one type, not [int]int and [int]c
# (maps of comparable values of two types join at [int]comparable; a class
# that is not <unique> is not comparable)
c := class{}
Main():void =
    X := ConcatenateMaps(map{1 => 1}, map{1 => c{}})
