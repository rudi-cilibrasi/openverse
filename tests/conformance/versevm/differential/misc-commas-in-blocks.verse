# Commas in a block make a tuple: option{1, 2} holds (1, 2) and a for body
# {X, X * X} gives an array of pairs.
# Tests LANGUAGE.md, Supported, Blocks: "in a block, statements that commas
# join on a line are a tuple (ch. 1, "Semicolons vs Commas", and its tests,
# SemicolonsVsCommas.versetest 70, 95, 100: ... option{1, 2} holds (1, 2),
# for (X := 1..2) {3, X} is an array of pairs)". The other reading (commas
# separate statements) would hold 2 and give an array of ints.
# OpenVerse prints (Lean and C agree):
#   option 1 2 | for 3 3 9
Main():void =
    O := option{1, 2}
    if (T := O?):
        Print("OVPROBE option {T(0)} {T(1)}")
    Pairs := for (X := 1..3) {X, X * X}
    if (P := Pairs[2]):
        Print("OVPROBE for {Pairs.Length} {P(0)} {P(1)}")
