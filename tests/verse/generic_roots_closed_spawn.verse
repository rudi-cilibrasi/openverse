# a spawn whose arguments have closed types needs no copy, so recursion at bigger types stays allowed (#174)
Report(N:int)<suspends>:int =
    Sleep(0.5)
    N
Nest(Items:[]t, D:int where t:type)<suspends>:int =
    T := spawn{Report(Items.Length)}
    if (D > 0) then Nest(array{Items}, D - 1) + T.Await() else T.Await()
Main()<suspends>:void = Print("{Nest(array{1, 2}, 2)}")
