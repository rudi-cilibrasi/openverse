# a spawned dispatch to an override with a narrower result type (#173)
thing := class:
    N:int
    Who():string = "thing"
sub_thing := class(thing):
    Who<override>():string = "sub"
maker := class:
    Make()<suspends>:thing = thing{N := 1}
sub_maker := class(maker):
    Make<override>()<suspends>:sub_thing =
        Sleep(1.0)
        sub_thing{N := 2}
Main()<suspends>:void =
    M:maker = sub_maker{}
    T := spawn{M.Make()}
    X := T.Await()
    Print("{X.N} {X.Who()}")
