import OpenVerse.Front.Parser

/-! Parse-only driver of the Book test harness (`booktests.py`).

`lake env lean --run tests/conformance/book/ParseOnly.lean LIST` reads the
paths in the file LIST, one per line, parses each with openverse's parser
(`parseProgram`, the parser `openverse check` runs first) and prints one line
per path: the path, a tab, and `ok` or `err` with the parser's message. -/

open OpenVerse.Front

def main (args : List String) : IO UInt32 := do
  let [list] := args | IO.eprintln "usage: ParseOnly.lean LIST"; return 2
  let out ← IO.getStdout
  for path in (← IO.FS.readFile list).splitOn "\n" do
    if path.isEmpty then continue
    let src ← IO.FS.readFile path
    match parseProgram src with
    | .ok _ => out.putStrLn s!"{path}\tok"
    | .error e => out.putStrLn s!"{path}\terr\t{(e.replace "\n" " ").replace "\t" " "}"
  return 0
