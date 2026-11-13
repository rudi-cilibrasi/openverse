/-
  OpenVerse front end — programs of several files (#27).

  `using{"relative_path"}` imports a file or a directory, relative to the
  importing file; a directory is one module, assembled from its entries in
  sorted order. openverse
  has no module namespaces yet, so it reads both flatly: every loaded file's
  definitions join one top level, each file is loaded once (import cycles are
  harmless), and subdirectories are flattened.

  In a directory:
  * names starting with `.`, names containing `.ignore`, and files with no
    `.` are skipped;
  * `Self.verse` and every other `.verse` file contribute their definitions;
  * `Name.txt` is the constant `Name:string`, `Name.value` the constant
    `Name := (contents)`, `Name.bin` the constant `Name:[]int` of its bytes
    (openverse has no `nat8`);
  * other files are ignored.
-/
import OpenVerse.Front.Parser

namespace OpenVerse.Front

/-- The loaded definitions so far, the files already loaded, and whether any
    of them mentions `Args`. -/
structure LoadSt where
  tops : Array STop := #[]
  seen : List String := []
  mentionsArgs : Bool := false

abbrev LoadM := StateT LoadSt (ExceptT String IO)

def loadErr (msg : String) : LoadM α := throw msg

/-- `p` relative to the main file's directory, for error positions. -/
def shownPath (main p : System.FilePath) : String :=
  let dir := (main.parent.getD ".").toString
  let s := p.toString
  if dir != "." && s.startsWith (dir ++ "/") then (s.drop (dir.length + 1)).toString else s

mutual
/-- Load the file or directory `p` once (`main` is the program's main path:
    its own positions are shown without a file name). -/
partial def loadPath (main p : System.FilePath) : LoadM Unit := do
  let canon ← (IO.FS.realPath p : IO System.FilePath)
  if (← get).seen.contains canon.toString then return
  modify fun st => { st with seen := canon.toString :: st.seen }
  if ← p.isDir then loadDir main p else loadFile main p

partial def loadFile (main f : System.FilePath) : LoadM Unit := do
  let shown := if f == main then "" else shownPath main f
  let pre := if shown.isEmpty then "" else shown ++ ":"
  let bytes ← (IO.FS.readBinFile f : IO ByteArray)
  let src ← match decodeSource bytes with
    | .ok s => pure s
    | .error e => loadErr s!"{pre}{e}"
  if (src.splitOn "Args").length > 1 then modify fun st => { st with mentionsArgs := true }
  let (tops, imps) ← match parseProgramImports src shown with
    | .ok r => pure r
    | .error e => loadErr s!"{pre}{e}"
  -- the imports first, then the file's own definitions
  for (pos, rel) in imps do
    let target := (f.parent.getD ".") / rel
    let target ← if ← target.pathExists then pure target
      else if ← (target.addExtension "verse").pathExists then pure (target.addExtension "verse")
      else loadErr s!"{pos.show}: cannot import \"{rel}\": no such file or directory"
    loadPath main target
  modify fun st => { st with tops := st.tops ++ tops.toArray }

partial def loadDir (main d : System.FilePath) : LoadM Unit := do
  let entries ← (d.readDir : IO (Array IO.FS.DirEntry))
  let sorted := entries.qsort fun a b => a.fileName < b.fileName
  for e in sorted do
    let n := e.fileName
    if n.startsWith "." || (n.splitOn ".ignore").length > 1 then continue
    if ← e.path.isDir then loadPath main e.path; continue
    let parts := n.splitOn "."
    if parts.length < 2 then continue
    let name := parts.head!
    let ext := parts.getLast!
    let pos : Pos := { line := 1, col := 0, file := shownPath main e.path }
    match ext with
    | "verse" => loadPath main e.path
    | "txt" =>
      let bytes ← (IO.FS.readBinFile e.path : IO ByteArray)
      let some text := String.fromUTF8? bytes | loadErr s!"{pos.file}: not UTF-8"
      let top := STop.const pos name [] (some (.name "string")) (.str pos [.text text])
      modify fun st => { st with tops := st.tops.push top }
    | "value" =>
      let bytes ← (IO.FS.readBinFile e.path : IO ByteArray)
      let some text := String.fromUTF8? bytes | loadErr s!"{pos.file}: not UTF-8"
      match parseExprText text.trimAscii.toString with
      | .ok v =>
        modify fun st => { st with tops := st.tops.push (.const pos name [] none v) }
        -- (an expression with `/`: the rational helpers, #116)
        if textUsesRational text then
          modify fun st => { st with tops := st.tops.push (.const pos ratMarker [] none (.block pos [])) }
      | .error err => loadErr s!"{pos.file}:{err}"
    | "bin" =>
      let bytes ← (IO.FS.readBinFile e.path : IO ByteArray)
      let elems := bytes.toList.map fun b => SExpr.int pos b.toNat
      let top := STop.const pos name [] (some (.arr (.name "int"))) (.arrayLit pos elems)
      modify fun st => { st with tops := st.tops.push top }
    | _ => pure ()
end

/-- The definitions of the program at `path`, a file or a directory, and of
    everything it imports; and whether it mentions `Args`. -/
def loadProgram (path : System.FilePath) : IO (Except String (List STop × Bool)) := do
  match ← ((loadPath path path).run {}).run with
  | .ok ((), st) => return .ok (st.tops.toList, st.mentionsArgs)
  | .error e => return .error e

end OpenVerse.Front
