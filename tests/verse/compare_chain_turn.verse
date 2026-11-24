# (#724) A comparison chain that turns from `>` or `>=` to `<` or `<=`
# groups from the left, as on Epic's Verse VM (UEFN 43.12, 2026-11-20:
# differential/prec-compare-chain and prec-compare-chain-mixed): a
# comparison yields its left operand, so `5 > 1 < 3` is `(5 > 1) < 3`, that
# is `5 < 3`, which fails. A chain in one direction checks every adjacent
# pair. openverse checked adjacent pairs throughout.
# Not settled by the probes, and kept as chains: `<` or `<=` then `>` or `>=`
# (`1 < 5 > 3`, which Epic's parser reads as brackets, 3100) and `=` in a
# chain.
Yn(B:logic):string = if (B?) then "y" else "n"

Tick(S:string, V:int)<transacts>:int =
    Print("eval {S}")
    V

Main():void =
    # the probes' items, in their order
    Print("{Yn(logic{1 < 2 < 3})} {Yn(logic{3 < 5 < 4})} {Yn(logic{5 > 1 < 3})} {Yn(logic{1 <= 1 <= 2 < 3})} ne {Yn(logic{1 <> 2 <> 1})} {Yn(logic{1 <> 2 <> 3})}")
    Print("mixed {Yn(logic{5 > 1 < 3})} {Yn(logic{3 < 5 < 4})} {Yn(logic{5 > 3 > 4})} {Yn(logic{3 > 1 < 2})} {Yn(logic{4 >= 4 < 5})} {Yn(logic{3 > 1 <= 1})} {Yn(logic{9 > 1 < 5})} {Yn(logic{2 > 1 < 5})}")
    V3 := if (W := (2 < 5 < 9)) then W else -1
    V4 := if (W := (9 > 5 > 2)) then W else -1
    V8 := if (W := (9 > 1 < 5)) then W else -1
    V9 := if (W := (2 > 1 < 5)) then W else -1
    Print("values {V3} {V4} {V8} {V9}")
    Print("grouped {Yn(logic{(5 > 1) < 3})} {Yn(logic{5 > (1 < 3)})}")
    # `>=` turns as `>` does, and the chain goes on from the left operand
    Print("more {Yn(logic{3 >= 1 < 2})} {Yn(logic{3 >= 3 <= 3})} {Yn(logic{2 > 1 < 5 < 9})} {Yn(logic{2 > 1 < 5 < 4})} {Yn(logic{9 > 5 > 1 < 3})} {Yn(logic{2 > 1 > 0 < 3})}")
    # kept: the other turn is a chain
    Print("kept {Yn(logic{1 < 5 > 3})} {Yn(logic{1 < 5 > 7})}")
    # each operand once, in the order written
    if (Tick("a", 2) > Tick("b", 1) < Tick("c", 5) <= Tick("d", 5)):
        Print("2 > 1 < 5 <= 5")
    var X:float = 2.5
    Print("float {Yn(logic{X > 1.0 < 2.0})} {Yn(logic{X > 1.0 < 3.0})}")
