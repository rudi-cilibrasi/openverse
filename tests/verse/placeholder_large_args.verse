# A variable of a class type at deeply nested type arguments (its type's name
# over 400 characters, the cut-off for instantiations that grow without
# end): it starts as an object of a class below, as a smaller one does; the
# cut-off is only for a type larger than one it is inside (#157)
i0(p0:type, p1:type) := interface:
    Get(X:p1)<suspends>:p0
    Tag():string
c1(t0:type) := class(i0(tuple(t0, t0), t0)):
    V:tuple(t0, t0)
    Get<override>(X:t0)<suspends>:tuple(t0, t0) =
        Sleep(0.0)
        V
    Tag<override>():string = "c1"
c2(u0:type) := class(c1(tuple(?u0, []u0))):
    Tag<override>():string = "c2"
c3(u0:type, u1:type) := class(c2(tuple([]u0, tuple(u1, int)))):
    Tag<override>():string = "c3"
c4(u0:type) := class(c3(u0, []u0)):
    Tag<override>():string = "c4"
G_i0(B:i0(p0, p1), Y:p1 where p0:type, p1:type)<suspends>:p0 = B.Get(Y)
Main()<suspends>:void =
    X42 := G_i0(c3(tuple(tuple(int, char), []char), []int){V := ((option{(array{((49, 'y'), array{'y', 'z'}), ((0, 'z'), array{'z', 'a'})}, (array{49, 0}, 49))}, array{(array{((0, 'z'), array{'z', 'a'}), ((1, 'a'), array{'a', 'b'})}, (array{0, 1}, 0)), (array{((1, 'a'), array{'a', 'b'}), ((2, 'b'), array{'b', 'c'})}, (array{1, 2}, 1))}), (option{(array{((0, 'z'), array{'z', 'a'}), ((1, 'a'), array{'a', 'b'})}, (array{0, 1}, 0))}, array{(array{((1, 'a'), array{'a', 'b'}), ((2, 'b'), array{'b', 'c'})}, (array{1, 2}, 1)), (array{((2, 'b'), array{'b', 'c'}), ((3, 'c'), array{'c', 'd'})}, (array{2, 3}, 2))}))}, (option{(array{((48, 'x'), array{'x', 'y'}), ((49, 'y'), array{'y', 'z'})}, (array{48, 49}, 48))}, array{(array{((49, 'y'), array{'y', 'z'}), ((0, 'z'), array{'z', 'a'})}, (array{49, 0}, 49)), (array{((0, 'z'), array{'z', 'a'}), ((1, 'a'), array{'a', 'b'})}, (array{0, 1}, 0))}))
    Print("ok")
