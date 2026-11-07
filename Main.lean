import OpenVerse
open OpenVerse

def errName : ErrKind → String
  | .overflow => "overflow" | .type => "type" | .slot => "slot" | .call => "call"
  | .control => "control" | .user => "user"

/-- Run a program and report per the exit protocol of docs/FORMAT.md. -/
def runProg (P : Prog) (fuel : Nat) : IO UInt32 := do
  match P.run fuel with
  | none =>
    IO.eprintln "limit: fuel exhausted"; return 3
  | some (r, out) =>
    let stdout ← IO.getStdout
    stdout.write (ByteArray.mk (out.map (·.toUInt8)).toArray)
    stdout.flush
    match r with
    | .ok _ | .ret _ => return 0
    | .fail => IO.eprintln "failure"; return 1
    | .brk => IO.eprintln "error: control"; return 2
    | .err k => IO.eprintln s!"error: {errName k}"; return 2

def usage : String :=
  "usage: openverse run FILE.verse [--fuel N] [ARG…] [do EXPR]\n" ++
  "                                               run Main() (or EXPR) with the reference interpreter;\n" ++
  "                                               the ARGs are the program's Args:[]string\n" ++
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
  | .ok (tops, mentionsArgs) => return Front.compileTops tops args mentionsArgs doExpr

def withProg (file : String) (k : Prog → IO UInt32) : IO UInt32 := do
  match ← loadAndCompile file [] none with
  | .error e => IO.eprintln s!"{file}:{e}"; return 4
  | .ok P => k P

/-- The shell arguments of `run`/`emit` (spec: expected tooling): the ARGs,
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

def main (args : List String) : IO UInt32 := do
  match args with
  | ["examples"] =>
    for (n, _) in Examples.all do IO.println n
    return 0
  | ["example", name] =>
    match Examples.all.lookup name with
    | some P => runProg P defaultFuel
    | none => IO.eprintln s!"no example {name}"; return 4
  | ["example", name, "--emit", file] =>
    match Examples.all.lookup name with
    | some P => IO.FS.writeBinFile file P.encode; return 0
    | none => IO.eprintln s!"no example {name}"; return 4
  | "run" :: file :: "--fuel" :: n :: rest => withProgArgs file rest (runProg · n.toNat!)
  | "run" :: file :: rest => withProgArgs file rest (runProg · defaultFuel)
  | "emit" :: file :: "-o" :: out :: rest => withProgArgs file rest fun P => do
      IO.FS.writeBinFile out P.encode; return 0
  | ["check", file] => withProg file fun P => do
      IO.println s!"ok: {P.fns.length} functions, Main = {P.main}"; return 0
  | ["core", file] => withProg file fun P => do
      for (fn, i) in P.fns.zip (List.range P.fns.length) do
        IO.println s!"fn {i} {fn.name} arity={fn.arity} slots={fn.nslots} decides={fn.decides}"
        IO.println s!"  {repr fn.body}"
      return 0
  | ["gen", seed] => runProg (Gen.program seed.toNat!) defaultFuel
  | ["gen", seed, "--emit", file] => do
      IO.FS.writeBinFile file (Gen.program seed.toNat!).encode; return 0
  | ["gen", seed, "--core"] => do
      let P := Gen.program seed.toNat!
      for fn in P.fns do IO.println s!"{fn.name} arity={fn.arity} slots={fn.nslots} decides={fn.decides}\n  {repr fn.body}"
      return 0
  | _ => IO.eprintln usage; return 4
