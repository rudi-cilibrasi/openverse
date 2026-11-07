#!/usr/bin/env python3
"""Random Verse programs for scripts/fuzz-fields.sh (#50), the even seeds:
class fields holding arrays, with objects allocated in conditions that fail,
methods writing Self, setter loops, deep recursion with a context at every
level, recursion in <decides> functions, and wrappers that call before they
allocate (calls with equal heap marks)."""
import random
import sys

HDR = '''box := class:
    var A:[]int = array{}
    var T:[]int = array{}
    var K:?box = false
    var Bs:[]box = array{}
    Put(X:int):int =
        set A = A + array{X}
        X
    Swap():int =
        L := A
        set A = T
        set T = L + array{1}
        0

Show(A:[]int):string =
    var S:string = ""
    for (X : A) { set S = "{S}{X}," }
    S

Dump(B:box):void =
    Print("A[{Show(B.A)}] T[{Show(B.T)}]")
    if (K := B.K?) then Print("K[{Show(K.A)}]") else Print("K-")
    for (Q : B.Bs) { Print("Bs[{Show(Q.A)}]") }

Deep(B:box, C:box, N:int):int =
    if (N > 0):
        set B.A = B.A + array{N}
        if (Deep(C, B, N - 1) > 1000) {}
        if (N > 3, Deep(B, C, Mod[N, 3] or 0) > N) {}
        set C.T = (for (X : B.A, X > 1) { X })
    N

DeepD(B:box, C:box, N:int)<decides>:void =
    set B.A = array{N} + C.T
    if (N > 0):
        DeepD[C, B, N - 1]
    else:
        N > 0

Id(B:box, C:box, N:int):int = Deep(B, C, N)

R(B:box, N:int):int =
    if (N > 0):
        set B.A = B.A + array{N}
        R(B, N - 1)
    N
'''


class G:
    def __init__(self, rnd):
        self.r = rnd
        self.tmp = 0

    def obj(self):
        return self.r.choice(['B', 'C'])

    def nexp(self):
        return self.r.choice(['N', 'N + 1', 'N - 1', '2', '5'])

    def arr(self, d=0):
        r = self.r
        p = self.obj()
        k = r.randrange(8 if d < 2 else 5)
        if k == 0:
            return 'array{%s, %d}' % (self.nexp(), r.randrange(10))
        if k == 1:
            return '%s.A + array{%s}' % (p, self.nexp())
        if k == 2:
            return '%s.T' % p
        if k == 3:
            return 'array{}'
        if k == 4:
            return '%s.A + %s.T' % (p, self.obj())
        if k == 5:
            return '(for (X : %s.A) { X + 1 })' % p
        if k == 6:
            return '(for (X : %s.A, X > %d) { X })' % (p, r.randrange(5))
        return '%s.T + array{%s}' % (p, self.nexp())

    def call_args(self):
        return '%s, %s, %s' % (self.obj(), self.obj(), self.nexp())

    def stmt(self, fi, fns, ind, d=0):
        r = self.r
        p = self.obj()
        q = self.obj()
        lower = [f for f in fns[:fi]]
        ds = [f for f in lower if f[1]]
        fs = [f for f in lower if not f[1]]
        k = r.randrange(23)
        if k >= 17:
            k = 17
        pad = '    ' * ind
        if k <= 2:
            return [pad + 'set %s.%s = %s' % (p, r.choice('AAT'), self.arr(d))]
        if k == 3:
            return [pad + 'set %s.K = option{box{A := %s}}' % (p, self.arr(d))]
        if k == 4:
            return [pad + 'set %s.Bs = %s.Bs + array{box{A := %s}}' % (p, q, self.arr(d))]
        if k == 5:
            return [pad + 'if (Kk := %s.K?) { set Kk.A = %s }' % (p, self.arr(d))]
        if k == 6:
            return [pad + 'for (Q : %s.Bs) { set Q.A = Q.A + array{%s} }' % (p, self.nexp())]
        if k == 7:
            self.tmp += 1
            return [pad + 'Tmp%d := array{N, N, N, N, N, N, N}' % self.tmp]
        if k == 8 and fs:
            f = r.choice(fs)
            return [pad + '%s(%s)' % (f[0], self.call_args())]
        if k == 9 and ds:
            f = r.choice(ds)
            return [pad + 'if (%s[%s]) {}' % (f[0], self.call_args())]
        if k == 10:
            return [pad + 'if (set %s.A = %s, N > %d) {}' % (p, self.arr(d), r.randrange(6))]
        if k == 11 and fs and ds:
            f = r.choice(fs)
            g = r.choice(ds)
            return [pad + 'if (%s(%s) > %d, %s[%s]) {}' % (f[0], self.call_args(), r.randrange(6),
                                                          g[0], self.call_args())]
        if k == 12:
            return [pad + 'for (X : %s.A, set %s.A = %s.A + array{X}, X > %d) {}' % (p, q, q, r.randrange(6))]
        if k == 13 and ds:
            g = r.choice(ds)
            return [pad + 'for (X : %s.A, %s[%s, %s, X]) {}' % (p, g[0], self.obj(), self.obj())]
        if k == 14:
            return [pad + 'R(%s, %d)' % (p, r.randrange(4))]
        if k == 15 and d < 2:
            # nested context with statements inside, then maybe fail
            body = []
            for _ in range(r.randrange(1, 3)):
                body += self.stmt(fi, fns, ind + 1, d + 1)
            self.tmp += 1
            body.append(pad + '    Z%d := 0' % self.tmp)
            return ([pad + 'if (' + self.cond(fi, fns, d) + '):'] + body +
                    [pad + 'else:', pad + '    ' + 'set %s.T = %s' % (p, self.arr(d)), pad + '    Y%d := 0' % self.tmp])
        if k == 16:
            self.tmp += 1
            return [pad + 'L%d := %s.A' % (self.tmp, p),
                    pad + 'set %s.A = %s' % (q, self.arr(d)),
                    pad + 'set %s.T = L%d + array{%s}' % (p, self.tmp, self.nexp())]
        if k == 17 and r.random() < 0.8:
            j = r.randrange(9)
            if j == 0:
                return [pad + 'if (Nb := box{A := %s}, set %s.K = option{Nb}, %s(Nb, %s, %s) > %d) {}' % (self.arr(d), p, r.choice([f[0] for f in fs] or ['Id']), q, self.nexp(), r.randrange(6))]
            if j == 1:
                return [pad + 'if (Nb := box{A := %s}, set %s.Bs = %s.Bs + array{Nb}, Nb.Put(%s) > %d) {}' % (self.arr(d), p, p, self.nexp(), r.randrange(6))]
            if j == 2:
                return [pad + 'Deep(%s, %s, %d)' % (p, q, r.randrange(70))]
            if j == 3:
                return [pad + 'if (DeepD[%s, %s, %d]) {}' % (p, q, r.randrange(6))]
            if j == 4:
                return [pad + 'for (Q : %s.Bs) { Q.Put(%s) }' % (p, self.nexp())]
            if j == 5:
                return [pad + '%s.Swap()' % p]
            if j == 6:
                return [pad + 'Id(%s, %s, %s)' % (p, q, self.nexp())]
            if j == 7:
                self.tmp += 1
                return [pad + 'var I%d:int = 0' % self.tmp, pad + 'loop:', pad + '    set I%d += 1' % self.tmp,
                        pad + '    %s.Put(I%d)' % (p, self.tmp), pad + '    if (I%d >= %d) { break }' % (self.tmp, r.randrange(1, 40))]
            return [pad + 'if (Kb := %s.K?, set Kb.K = option{%s}, Kb.Put(%s) > %d) {}' % (p, q, self.nexp(), r.randrange(6))]
        if k == 17 and fs and r.random() < 0.5:
            f = r.choice(fs)
            return [pad + 'if (%s(%s) > %d) {}' % (f[0], self.call_args(), r.randrange(7))]
        if k == 17 and r.random() < 0.5:
            return [pad + 'set %s.%s = %s' % (p, r.choice(['A = array{}', 'T = array{}', 'K = false'])[0], r.choice(['A = array{}', 'T = array{}', 'K = false'])[4:])] if False else [pad + 'set %s.%s' % (p, r.choice(['A = array{}', 'T = array{}', 'K = false']))]
        if k == 17 and fs:
            f = r.choice(fs)
            return [pad + 'set %s.A = %s.A + array{%s(%s)}' % (p, q, f[0], self.call_args())]
        return [pad + 'set %s.A = %s' % (p, self.arr(d))]

    def cond(self, fi, fns, d):
        r = self.r
        ds = [f for f in fns[:fi] if f[1]]
        parts = []
        for _ in range(r.randrange(1, 3)):
            k = r.randrange(3)
            if k == 0 and ds:
                parts.append('%s[%s]' % (r.choice(ds)[0], self.call_args()))
            elif k == 1:
                parts.append('set %s.A = %s' % (self.obj(), self.arr(d)))
            else:
                parts.append('N > %d' % r.randrange(6))
        if not any(x.startswith('N >') or '[' in x.split('=')[0] for x in parts):
            parts.append('N > %d' % r.randrange(6))
        return ', '.join(parts)


def gen(seed):
    r = random.Random(seed)
    g = G(r)
    nf = r.randrange(3, 7)
    fns = []
    for i in range(nf):
        fns.append(('F%d' % i if r.random() < 0.6 else 'D%d' % i, None))
    fns = [(n, n[0] == 'D') for n, _ in fns]
    out = [HDR]
    for i, (name, dec) in enumerate(fns):
        if dec:
            out.append('%s(B:box, C:box, N:int)<decides>:void =' % name)
        else:
            out.append('%s(B:box, C:box, N:int):int =' % name)
        for _ in range(r.randrange(2, 6)):
            out += g.stmt(i, fns, 1)
        if dec:
            out.append('    N %s %d' % (r.choice(['>', '<']), r.randrange(6)))
        else:
            out.append('    N')
        out.append('')
    out.append('Main():void =')
    out.append('    B := box{}')
    out.append('    C := box{}')
    out.append('    N:int = 3')
    allf = fns + [('Wrap', False)]
    for _ in range(r.randrange(2, 6)):
        out += g.stmt(len(fns), fns, 1)
    out.append('    Tz := array{9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9}')
    out.append('    Dump(B)')
    out.append('    Dump(C)')
    return '\n'.join(out) + '\n'


if __name__ == '__main__':
    sys.stdout.write(gen(int(sys.argv[1])))
