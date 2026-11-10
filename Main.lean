import OpenVerse
open OpenVerse

def errName : ErrKind → String
  | .overflow => "overflow" | .type => "type" | .slot => "slot" | .call => "call"
  | .control => "control" | .user => "user"

/-- The depth budget of `openverse run` (#97): how many non-tail calls the
    compiled interpreter may nest (`evalB`, `Core/Bounded.lean`). Each is one
    native frame of at most about 150 bytes. The Lean runtime runs `main` on a
    stack of 1 GiB, or `LEAN_STACK_SIZE_KB` KiB when that is set, whatever
    `ulimit -s` says. On the 1 GiB stack, programs that recurse forever
    (through calls, arguments, conditions, `for` bodies and filters,
    sequences, methods, constructions, …) overflowed it at 7.2 to 8.4 million
    calls, about 147 bytes each at worst; the budget allows 270 bytes a call,
    a margin of 1.8 (4 million calls on the default stack, just under a
    million levels of ordinary Verse recursion). Beyond it, `openverse run`
    reports `limit: recursion depth`, as `cverse` does past its own bound. -/
def maxDepth : IO Nat := do
  let kib := ((← IO.getEnv "LEAN_STACK_SIZE_KB").bind String.toNat?).getD 1048576
  return kib * 1024 / 270

/-- Run a program and report per the exit protocol of docs/FORMAT.md. -/
def runProg (P : Prog) (fuel : Nat) : IO UInt32 := do
  match P.runB fuel (← maxDepth) with
  | .deep =>
    IO.eprintln "limit: recursion depth"; return 3
  | .fuel =>
    IO.eprintln "limit: fuel exhausted"; return 3
  | .res (r, out) =>
    let stdout ← IO.getStdout
    stdout.write (ByteArray.mk (out.map (·.toUInt8)).toArray)
    stdout.flush
    match r with
    | .ok _ | .ret _ => return 0
    | .fail => IO.eprintln "failure"; return 1
    | .brk => IO.eprintln "error: control"; return 2
    | .err k => IO.eprintln s!"error: {errName k}"; return 2

def usage : String :=
  "usage: openverse run FILE.verse [--fuel N] [--emit FILE.vbc] [ARG…] [do EXPR]\n" ++
  "                                               run Main() (or EXPR) with the reference interpreter;\n" ++
  "                                               the ARGs are the program's Args:[]string; --emit also\n" ++
  "                                               writes what emit would, compiling the program once\n" ++
  "       openverse emit FILE.verse -o FILE.vbc [ARG…] [do EXPR]\n" ++
  "                                               compile to OVBC for the C runtime (cverse)\n" ++
  "       openverse check FILE.verse              parse, elaborate and check only\n" ++
  "       openverse core FILE.verse               print the elaborated Verse Core\n" ++
  "       openverse example NAME [--emit FILE.vbc] | openverse examples"

/-- Load a program, a file or a directory with everything it imports, and
    compile it: malformed UTF-8 is a front-end error (exit 4), as is any
    other front-end error. -/
def loadAndCompile (file : String) (args : List String) (doExpr : Option String) :
    IO (Except String Prog) := do
  match ← Front.loadProgram file with
  | .error e => return .error e
  | .ok (tops, mentionsArgs) =>
    -- (OPENVERSE_DEBUG=1: an internal error also prints the rejected Verse Core)
    let debug := (← IO.getEnv "OPENVERSE_DEBUG").any fun v => v != "" && v != "0"
    return Front.compileTops tops args mentionsArgs doExpr debug

def withProg (file : String) (k : Prog → IO UInt32) : IO UInt32 := do
  match ← loadAndCompile file [] none with
  | .error e => IO.eprintln s!"{file}:{e}"; return 4
  | .ok P => k P

/-- The shell arguments of `run`/`emit`: the ARGs,
    then `do` and an expression to run instead of `Main`. -/
def splitDo (rest : List String) : List String × Option String :=
  match rest.span (· != "do") with
  | (as, "do" :: e) => (as, some (" ".intercalate e))
  | (as, _) => (as, none)

def withProgArgs (file : String) (rest : List String) (k : Prog → IO UInt32) : IO UInt32 := do
  let (as, e) := splitDo rest
  match ← loadAndCompile file as e with
  | .error err => IO.eprintln s!"{file}:{err}"; return 4
  | .ok P => k P

def defaultFuel : Nat := 100000000

/-- `openverse run FILE [--fuel N] [--emit FILE.vbc] [ARG…] [do EXPR]`. With
    `--emit`, the bytecode `emit` would write is written before the program
    runs, from the same compilation, so the scripts that run a program on both
    implementations compile it once. -/
def runCmd (file : String) (fuel : Nat) (emit : Option String) : List String → IO UInt32
  | "--fuel" :: n :: rest => runCmd file n.toNat! emit rest
  | "--emit" :: out :: rest => runCmd file fuel (some out) rest
  | rest => withProgArgs file rest fun P => do
      if let some out := emit then IO.FS.writeBinFile out P.encode
      runProg P fuel

/-- The hand-written Core programs (`tests/core` holds their encodings). -/
def allExamples : List (String × Prog) := Examples.all ++ HeapExamples.all

def main (args : List String) : IO UInt32 := do
  match args with
  | ["examples"] =>
    for (n, _) in allExamples do IO.println n
    return 0
  | ["example", name] =>
    match allExamples.lookup name with
    | some P => runProg P defaultFuel
    | none => IO.eprintln s!"no example {name}"; return 4
  | ["example", name, "--emit", file] =>
    match allExamples.lookup name with
    | some P => IO.FS.writeBinFile file P.encode; return 0
    | none => IO.eprintln s!"no example {name}"; return 4
  | "run" :: file :: rest => runCmd file defaultFuel none rest
  | "emit" :: file :: "-o" :: out :: rest => withProgArgs file rest fun P => do
      IO.FS.writeBinFile out P.encode; return 0
  | ["check", file] => withProg file fun P => do
      IO.println s!"ok: {P.fns.length} functions, Main = {P.main}"; return 0
  | ["core", file] => withProg file fun P => do
      for (fn, i) in P.fns.zip (List.range P.fns.length) do
        IO.println s!"fn {i} {fn.name} arity={fn.arity} slots={fn.nslots} decides={fn.decides}"
        IO.println (fn.body.compact "  " (cap := 1000000))
      return 0
  | ["gen", seed] => runProg (Gen.program seed.toNat!) defaultFuel
  | ["gen", seed, "--emit", file] => do
      IO.FS.writeBinFile file (Gen.program seed.toNat!).encode; return 0
  | ["gen", seed, "--core"] => do
      let P := Gen.program seed.toNat!
      for fn in P.fns do IO.println s!"{fn.name} arity={fn.arity} slots={fn.nslots} decides={fn.decides}\n  {repr fn.body}"
      return 0
  | _ => IO.eprintln usage; return 4
