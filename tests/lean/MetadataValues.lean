import OpenVerse.Front.MetadataValues

open OpenVerse OpenVerse.Front.MetadataValues

private def expect (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def models : IO Unit := do
  let variance : Variances := fun _ _ => .inv
  let heap : HeapTy := [(0, [])]
  let dataTy := VTy.arr (.tup [.int, .opt (.arr .char)])
  let dataValue := Value.arr #[.tup [.int 7, .some (.arr #[.char 65])]]
  expect (hasTy variance heap dataValue dataTy && objectFree dataTy && !hasObjectRef dataValue)
    "typed nested immutable data needs no object identity"
  expect (objectFree VTy.void && !hasObjectRef .void) "void cannot carry an object alias"
  for (value, ty) in [
      (Value.ref 0, VTy.ref [0] []),
      (.some (.ref 0), .opt (.ref [0] [])),
      (.tup [.int 1, .ref 0], .tup [.int, .ref [0] []]),
      (.arr #[.ref 0], .arr (.ref [0] [])),
      (.arr #[.some (.tup [.ref 0])], .arr (.opt (.tup [.ref [0] []])))] do
    expect (hasTy variance heap value ty && !objectFree ty && hasObjectRef value)
      "literal prototype aliases must survive every immutable wrapper"
  for ty in [VTy.dyn, .var 0, .ref [] [.int], .vref [] [],
      .arr (.var 0), .opt .dyn, .tup [.int, .ref [0] []]] do
    expect (!objectFree ty) "opaque types and object references cannot certify alias-free slots"
  expect (hasTy variance heap .none (.opt (.ref [0] [])) &&
      !hasObjectRef .none && !objectFree (.opt (.ref [0] [])))
    "an empty current value does not make an object-bearing parameter type safe"
  IO.println "PASS object-free typed data, void, opaque types and nested literal prototype aliases"

private def scale : IO Unit := do
  let count := 32000
  let values := (List.range count).map fun i =>
    Value.tup [.int (Int.ofNat i), .some (.arr #[.char 65])]
  let preparedRef ← IO.mkRef values.toArray
  let values ← preparedRef.get
  let started ← IO.monoMsNow
  expect (!hasObjectRef (.arr values)) "large immutable data literal has no object aliases"
  let values := values.set! (count - 1) (.some (.arr #[.tup [.ref 0]]))
  expect (hasObjectRef (.arr values)) "a final nested prototype must not be lost in a large literal"
  IO.println s!"PASS {count}-element nested literal data/reference scans ({(← IO.monoMsNow) - started}ms)"

def main (args : List String) : IO Unit :=
  if args.contains "--scale" then scale else models
