# The seventh decimal digit of a float's ToString: ties and near-ties.
# Tests LANGUAGE.md, float: "the float's exact value rounded to a multiple of
# 10^-6, a tie to the even digit (98.500000, 1.234568 for 1.2345678901234567,
# 0.007812 for 0.0078125)". 0.0078125 (2^-7) and 0.0234375 (3 * 2^-7) are
# exact ties: half-to-even gives 0.007812 and 0.023438, half-up gives
# 0.007813 and 0.023438, half-away-from-zero for -0.0078125 gives -0.007813.
# 1.0000005 and 2.0000005 are not exact: their binary values fall just below
# or above the tie. The Book states no rule for the seventh digit.
# OpenVerse prints (Lean and C agree):
#   ties 0.007812 0.023438 -0.007812 0.039062
#   near 1.234568 1.000001 2.000001 0.000002
#   nines 1.000000 0.999999 10.000000 -1.000000
Main():void =
    Print("OVPROBE ties {0.0078125} {0.0234375} {-0.0078125} {0.0390625}")
    Print("OVPROBE near {1.2345678901234567} {1.0000005} {2.0000005} {0.0000015}")
    Print("OVPROBE nines {0.9999995} {0.99999949} {9.9999999} {-0.9999996}")
