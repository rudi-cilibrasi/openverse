# Setting array elements through a var: in range, out of range (a failure
# that changes nothing), and nested. (The value of a set: arr-set-value.)
# Tests LANGUAGE.md, Mutation: "set A[i] = e (fails out of range; returns
# e)", "set A[i][j] op= e"; "an index out of range ... fails".
# OpenVerse prints (Lean and C agree):
#   a 1,20,3 fails fails | b 1,9 8 fails
Show(A:[]int):string = Join(for (X : A) { "{X}" }, ",")

Main():void =
    var A:[]int = array{1, 2, 3}
    if (set A[1] = 20) {}
    P := if (set A[3] = 40) then "ok" else "fails"
    Q := if (set A[-1] = 50) then "ok" else "fails"
    Print("OVPROBE a {Show(A)} {P} {Q}")
    var G:[][]int = array{array{1, 2}, array{3}}
    if (set G[0][1] = 9, set G[1][0] += 5) {}
    R := if (set G[1][1] = 0) then "ok" else "fails"
    if (Row0 := G[0], Row1 := G[1]):
        Print("OVPROBE b {Show(Row0)} {Show(Row1)} {R}")
