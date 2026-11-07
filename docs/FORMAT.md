# OVBC: the binary format of a Verse Core program

The Lean front end (`openverse emit`) writes this format; the C runtime
(`cverse`) loads it. It is a direct serialisation of `OpenVerse.Core.Prog`
(`OpenVerse/Core/Syntax.lean`), defined by `OpenVerse/Core/Encode.lean`.

All integers are little-endian. `u8`, `u32` are unsigned; `i64` is two's
complement.

```
File   := "OVBC" version:u32(=1) nfns:u32 main:u32 Fn[nfns]
Fn     := arity:u32 nslots:u32 decides:u8 namelen:u32 name:u8[namelen]
          nnodes:u32 Node[nnodes] root:u32
Node   := tag:u8 payload
```

Each function has its own node table, numbered from 0 in file order. A node
refers to its children by index **into the same table**, and every child
index must be **smaller than the index of the node** that refers to it. So
the table is in post-order, every reference points backwards, and the loader
can check the whole program in one forward pass. `root` is the body of the
function.

| tag | node | payload | Verse Core |
|---|---|---|---|
| 0 | LIT | `Lit` | `.lit v` |
| 1 | LOCAL | `slot:u32` | `.local slot` |
| 2 | ASSIGN | `slot:u32 e:u32` | `.assign slot e` |
| 3 | SEQ | `a:u32 b:u32` | `.seq a b` |
| 4 | PRIM | `prim:u8 k:u32 n:u32 args:u32[n]` | `.prim op args` (`k` is the index of `tupGet`, else 0) |
| 5 | CALL | `fn:u32 n:u32 args:u32[n]` | `.call fn args` |
| 6 | ITE | `c:u32 t:u32 e:u32` | `.ite c t e` |
| 7 | FOR | `slot:u32 it:u32 filt:u32 body:u32` | `.forE slot it filt body` |
| 8 | LOOP | `b:u32` | `.loop b` |
| 9 | BRK | — | `.brk` |
| 10 | RET | `e:u32` | `.ret e` |
| 11 | PRINT | `e:u32` | `.print e` |
| 12 | HEAP | `op:u8 k:u32 n:u32 args:u32[n]`, or for `op` 4 `op:u8 m:u32 us:u32[m] n:u32 args:u32[n]` | `.heap op args` (`op`: 0 `new k`, 1 `get k`, 2 `set k`, 3 `tag` with `k = 0`, 4 `isTag us`) |

```
Lit := 0 INT  i:i64
     | 1 LOGIC b:u8 (0 or 1)
     | 2 CHAR c:u8
     | 3 STR  n:u32 bytes:u8[n]       -- .arr of n chars (also the empty array)
     | 4 NONE                         -- the empty option (`false`)
     | 5 VOID                         -- .tup []
     | 6 REF  a:u32                   -- .ref a (only fuzzing makes these: no typed program has one)
```

A literal that is not one of these (a non-string array, a non-empty tuple,
`some v`) is encoded as the `PRIM` node that builds it (`mkArr`, `mkTup`,
`mkSome`) applied to literal children. That evaluates to the same value
(`Prim.apply .mkArr vs = .ok (.arr vs)`), and it keeps every node flat, so the
loader needs no recursion.

## Primitive codes

| code | prim | code | prim | code | prim |
|---|---|---|---|---|---|
| 0 | add | 10 | le | 20 | index |
| 1 | sub | 11 | gt | 21 | len |
| 2 | mul | 12 | ge | 22 | arrSet |
| 3 | neg | 13 | eq | 23 | flatten |
| 4 | abs | 14 | ne | 24 | range |
| 5 | floorDiv | 15 | query | 25 | tupGet (k) |
| 6 | ceilDiv | 16 | mkArr | 26 | toStr |
| 7 | quotient | 17 | mkTup | 27 | fail |
| 8 | modulo | 18 | mkSome | 28 | userErr |
| 9 | lt | 19 | concat | | |

## What the loader accepts

`vx_load` (`runtime/src/load.c`) accepts a buffer exactly when it parses to
the end with no bytes left over and:

1. the magic is `OVBC`, the version is 1, `nfns ≥ 1`, `main < nfns`;
2. every function has `arity ≤ nslots`, `nnodes ≥ 1` and `root < nnodes`;
3. every child index of node `j` is `< j`;
4. every slot (LOCAL, ASSIGN, FOR) is `< nslots` of its function;
5. every CALL names a function `< nfns` whose `arity` equals the call's `n`;
6. every PRIM code is `≤ 28`, `k = 0` unless the code is 25, every LIT
   tag is `≤ 6` with LOGIC `≤ 1`, and every HEAP op is `≤ 4`, with `k = 0`
   for `tag`;
7. the counts stay within the limits in `runtime/include/openverse.h`.

Conditions 2, 4 and 5 are `OpenVerse.Prog.WellScoped`
(`OpenVerse/Core/Scoping.lean`). By `Eval.scoped_ok`, a program the loader
accepts never raises a slot or call error and never changes the size of a
frame.
Condition 3 means every node's children come before it, so the node graph is
acyclic. The loader does not check the number of arguments of a HEAP node,
nor the number of fields of `new` against a class: like a PRIM applied to
the wrong values, those are type errors at run time (`HeapOp.apply`), which
typed programs never have. Class tags, field indices and REF literals are
`u32`: `Prog.encode` writes a larger number modulo 2^32, so the encoding of
a Core program with one is not that program. The front end numbers classes
and fields from 0, and no typed program has a REF literal, so no compiled
program needs more. The QuickProof law `loader_wellscoped`
(`proofs/quickproof/loader`) proves that the C loader enforces conditions 1–7
for every input buffer, and reads only inside the buffer.

## Exit protocol (both implementations)

| exit | meaning | stderr |
|---|---|---|
| 0 | `Main` succeeded | — |
| 1 | `Main` failed (only a `<decides>` `Main` can) | `failure` |
| 2 | runtime error | `error: overflow` / `type` / `slot` / `call` / `control` / `user` |
| 3 | resource limit (fuel, recursion depth, memory) | `limit: …` |
| 4 | the program could not be loaded or compiled | the reason |

stdout is exactly the bytes the program printed.

The format does not carry `Fn.writes` (#35): it is a fact the front end
proves about a program (`Prog.checkWriteSound`), not part of its meaning,
and the runtime never needs it.
