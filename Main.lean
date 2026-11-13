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
  "usage: openverse run FILE.verse [--no-choice] [--event-fifo] [--signal-no-rollback] [--extended-defaults] [--fuel N] [--emit FILE.vbc] [ARG…] [do EXPR]\n" ++
  "                                               run Main() (or EXPR) with the reference interpreter;\n" ++
  "                                               the ARGs are the program's Args:[]string; --emit also\n" ++
  "                                               writes what emit would, compiling the program once\n" ++
  "       openverse emit FILE.verse [--no-choice] [--event-fifo] [--signal-no-rollback] [--extended-defaults] -o FILE.vbc [ARG…] [do EXPR]\n" ++
  "                                               compile to OVBC for the C runtime (cverse)\n" ++
  "       openverse check FILE.verse [--no-choice] [--event-fifo] [--signal-no-rollback] [--extended-defaults]\n" ++
  "                                               parse, elaborate and check only\n" ++
  "       openverse core FILE.verse [--no-choice] [--event-fifo] [--signal-no-rollback] [--extended-defaults]\n" ++
  "                                               print the elaborated Verse Core\n" ++
  "       --no-choice excludes |, first, for/generators and ranges from all loaded source;\n" ++
  "       it may also precede the command or file. In run/emit, -- passes literal Args.\n" ++
  "       --event-fifo resumes the tasks an event's Signal wakes in the order they began to wait (#513).\n" ++
  "       --signal-no-rollback refuses an event's Signal that a failure context may call (#515).\n" ++
  "       --extended-defaults retains extended field defaults without a convergence assertion (#511).\n" ++
  "       openverse example NAME [--emit FILE.vbc] | openverse examples"

/-- The compiler's opt-in semantic policies: FIFO event resumption (#513,
    `--event-fifo`), no event signal in a failure context (#515,
    `--signal-no-rollback`), and extended field defaults kept without a
    convergence assertion (#511, `--extended-defaults`). -/
structure Policies where
  eventFifo : Bool := false
  signalNoRollback : Bool := false
  extendedDefaults : Bool := false

/-- Load a program, a file or a directory with everything it imports, and
    compile it: malformed UTF-8 is a front-end error (exit 4), as is any
    other front-end error. A program that compiles may have warnings, which
    are printed to standard error, `FILE:LINE:COL: warning: …`, before
    anything else is done with it; they change no exit status
    (docs/FORMAT.md, "Exit protocol"). -/
def loadAndCompile (file : String) (args : List String) (doExpr : Option String)
    (profile : Front.SourceProfile := .full) (pol : Policies := {}) :
    IO (Except String Prog) := do
  match ← Front.loadProgram file with
  | .error e => return .error e
  | .ok (tops, mentionsArgs) =>
    -- (OPENVERSE_DEBUG=1: an internal error also prints the rejected Verse Core)
    let debug := (← IO.getEnv "OPENVERSE_DEBUG").any fun v => v != "" && v != "0"
    match Front.compileTopsWarned tops args mentionsArgs doExpr debug profile pol.eventFifo
        (extendedDefaults := pol.extendedDefaults) (signalNoRollback := pol.signalNoRollback) with
    | .error e => return .error e
    | .ok (P, warnings) =>
      for w in warnings do IO.eprintln s!"{file}:{w}"
      return .ok P

def withProg (file : String) (profile : Front.SourceProfile) (k : Prog → IO UInt32) (pol : Policies := {}) :
    IO UInt32 := do
  match ← loadAndCompile file [] none profile pol with
  | .error e => IO.eprintln s!"{file}:{e}"; return 4
  | .ok P => k P

/-- The shell arguments of `run`/`emit`: the ARGs,
    then `do` and an expression to run instead of `Main`. -/
def splitDo (rest : List String) : List String × Option String :=
  match rest.span (· != "do") with
  | (as, "do" :: e) => (as, some (" ".intercalate e))
  | (as, _) => (as, none)

def withProgArgs (file : String) (rest : List String) (profile : Front.SourceProfile)
    (k : Prog → IO UInt32) (literal : Bool := false) (pol : Policies := {}) : IO UInt32 := do
  let (as, e) := if literal then (rest, none) else splitDo rest
  match ← loadAndCompile file as e profile pol with
  | .error err => IO.eprintln s!"{file}:{err}"; return 4
  | .ok P => k P

def defaultFuel : Nat := 100000000

/-- `openverse run FILE [--fuel N] [--emit FILE.vbc] [ARG…] [do EXPR]`. With
    `--emit`, the bytecode `emit` would write is written before the program
    runs, from the same compilation, so the scripts that run a program on both
    implementations compile it once. -/
def runCmd (file : String) (fuel : Nat) (emit : Option String)
    (profile : Front.SourceProfile) (pol : Policies := {}) : List String → IO UInt32
  | "--no-choice" :: rest => runCmd file fuel emit .choiceFree pol rest
  | "--event-fifo" :: rest => runCmd file fuel emit profile { pol with eventFifo := true } rest
  | "--signal-no-rollback" :: rest => runCmd file fuel emit profile { pol with signalNoRollback := true } rest
  | "--extended-defaults" :: rest => runCmd file fuel emit profile { pol with extendedDefaults := true } rest
  | "--fuel" :: n :: rest => runCmd file n.toNat! emit profile pol rest
  | "--emit" :: out :: rest => runCmd file fuel (some out) profile pol rest
  | rest =>
    let (literal, rest) := match rest with | "--" :: rest => (true, rest) | _ => (false, rest)
    withProgArgs file rest profile (fun P => do
      if let some out := emit then IO.FS.writeBinFile out P.encode
      runProg P fuel) literal pol

/-- Source-profile options before the command, file or compiler options. -/
def profilePrefix (profile : Front.SourceProfile) : List String → Front.SourceProfile × List String
  | "--no-choice" :: rest => profilePrefix .choiceFree rest
  | rest => (profile, rest)

/-- `--no-choice` and the policies' options, in any order. -/
def optionsPrefix (profile : Front.SourceProfile) (pol : Policies) :
    List String → Front.SourceProfile × Policies × List String
  | "--no-choice" :: rest => optionsPrefix .choiceFree pol rest
  | "--event-fifo" :: rest => optionsPrefix profile { pol with eventFifo := true } rest
  | "--signal-no-rollback" :: rest => optionsPrefix profile { pol with signalNoRollback := true } rest
  | "--extended-defaults" :: rest => optionsPrefix profile { pol with extendedDefaults := true } rest
  | rest => (profile, pol, rest)

def emitCmd (file : String) (profile : Front.SourceProfile) (pol : Policies := {}) : List String → IO UInt32
  | "--no-choice" :: rest => emitCmd file .choiceFree pol rest
  | "--event-fifo" :: rest => emitCmd file profile { pol with eventFifo := true } rest
  | "--signal-no-rollback" :: rest => emitCmd file profile { pol with signalNoRollback := true } rest
  | "--extended-defaults" :: rest => emitCmd file profile { pol with extendedDefaults := true } rest
  | "-o" :: out :: rest =>
    let (profile, pol, rest) := optionsPrefix profile pol rest
    let (literal, rest) := match rest with | "--" :: rest => (true, rest) | _ => (false, rest)
    withProgArgs file rest profile (fun P => do
      IO.FS.writeBinFile out P.encode
      return 0) literal pol
  | _ => do IO.eprintln usage; return 4

/-- The hand-written Core programs (`tests/core` holds their encodings). -/
def allExamples : List (String × Prog) := Examples.all ++ HeapExamples.all

def main (args : List String) : IO UInt32 := do
  let (profile, args) := profilePrefix .full args
  let (profile, args) := match args with
    | command :: rest =>
      let (profile, rest) := profilePrefix profile rest
      (profile, command :: rest)
    | [] => (profile, [])
  if profile != .full && !(args.head?.any (["run", "emit", "check", "core"].contains ·)) then
    IO.eprintln "--no-choice selects a Verse source profile for run, emit, check or core"
    return 4
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
  | "run" :: file :: rest => runCmd file defaultFuel none profile {} rest
  | "emit" :: file :: rest => emitCmd file profile {} rest
  | ["gen", seed] => runProg (Gen.program seed.toNat!) defaultFuel
  | ["gen", seed, "--emit", file] => do
      IO.FS.writeBinFile file (Gen.program seed.toNat!).encode; return 0
  | ["gen", seed, "--core"] => do
      let P := Gen.program seed.toNat!
      for fn in P.fns do IO.println s!"{fn.name} arity={fn.arity} slots={fn.nslots} decides={fn.decides}\n  {repr fn.body}"
      return 0
  | command :: file :: rest =>
    if command == "check" || command == "core" then
      let (profile, pol, rest) := optionsPrefix profile {} rest
      if !rest.isEmpty then IO.eprintln usage; return 4
      withProg file profile (pol := pol) fun P => do
        if command == "check" then
          IO.println s!"ok: {P.fns.length} functions, Main = {P.main}"
        else
          for (fn, i) in P.fns.zip (List.range P.fns.length) do
            IO.println s!"fn {i} {fn.name} arity={fn.arity} slots={fn.nslots} decides={fn.decides}"
            IO.println (fn.body.compact "  " (cap := 1000000))
        return 0
    else IO.eprintln usage; return 4
  | _ => IO.eprintln usage; return 4
