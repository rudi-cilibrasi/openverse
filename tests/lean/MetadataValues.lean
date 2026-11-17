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

private def strictDataModels : IO Unit := do
  -- 0<->1 is an ordinary recursive data cycle; 2 is private, 3 metadata;
  -- 4/5 transitively reach them, 6/7 are opaque/unknown, 8 is empty data.
  let classes : Array (List VTy) := #[
    [.int, .ref [1] []], [.arr (.ref [0] [])], [.int], [.int],
    [.opt (.ref [2] [])], [.tup [.int, .ref [3] []]], [.var 0],
    [.ref [99] []], [], [.vref [(0,[])] []], [.dyn], [.ref [] []],
    [.ref [0] [.var 0]], [.ref [0,3] []]]
  let fields : Array (List Nat) := (Array.replicate classes.size []).set! 3 [0]
  let flags := dataClassFlags classes fields [2]
  expect (flags == #[true,true,false,false,false,false,false,false,true,false,false,false,false,false])
    "private, metadata, opaque and unknown barriers must propagate through every class edge"
  for ty in [VTy.int, .void, .ref [0] [], .arr (.opt (.ref [1,8] [])),
      .tup [.int,.ref [8] []], .ref [0] [.arr .int]] do
    expect (dataOnly flags ty) "closed ordinary recursive data should retain its strict certificate"
  for ty in [VTy.dyn,.var 0,.vref [(0,[])] [],.ref [] [],.ref [99] [],
      .ref [2] [],.ref [0,3] [],.arr (.ref [4] []),.opt (.ref [5] []),
      .ref [0] [.var 0],.ref [0] [.ref [2] []]] do
    expect (!dataOnly flags ty) "unsafe type arguments and reference variants must not be erased"
  expect (!objectFree (.ref [0] []) && dataOnly flags (.ref [0] []))
    "strict data certificate must not widen the existing alias-free theorem"
  -- Independently compute the greatest fixed point by whole-graph rescans.
  let graph : Array (List Nat) := #[[1],[0],[2],[4],[3],[0,3],[],[99]]
  let graphClasses := graph.map fun edges => edges.map fun tag => VTy.ref [tag] []
  let graphMetadata := Array.replicate graph.size ([] : List Nat)
  let actual := dataClassFlags graphClasses graphMetadata [4]
  let mut oracle := Array.replicate graph.size true
  oracle := oracle.set! 4 false
  for _ in [:graph.size] do
    oracle := graph.mapIdx fun index edges => oracle[index]! &&
      edges.all (fun target => oracle[target]?.getD false)
  expect (!(dataClassFlags #[[],[]] #[[]] [])[1]!)
    "a missing metadata-field table entry must fail closed"
  expect (actual == oracle) "reverse queue must match an independent finite-graph fixed point"
  let protos := #[true,false,true]
  for value in [Value.ref 0,.some (.ref 2),.arr #[.tup [.int 1,.ref 0]],.none] do
    expect (!hasUnsafeObjectRef protos value) "explicit safe prototypes survive nested wrappers"
  for value in [Value.ref 1,.ref 99,.some (.arr #[.tup [.ref 0,.ref 1]])] do
    expect (hasUnsafeObjectRef protos value) "unsafe or unknown prototype addresses must stay visible"
  IO.println "PASS strict data graph certificates, independent fixed point and nested prototype barriers"

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
  let classes := (List.range count).toArray.map fun index =>
    [VTy.ref [if index + 1 < count then index + 1 else 0] []]
  let classRef ← IO.mkRef classes
  let classes ← classRef.get
  let startedGraph ← IO.monoMsNow
  let closedMetadata := Array.replicate count ([] : List Nat)
  expect ((dataClassFlags classes closedMetadata []).all id) "large ordinary cycle remains safe"
  expect ((dataClassFlags classes closedMetadata [count - 1]).all (! ·)) "one private barrier propagates through a large cycle"
  let metadata := (Array.replicate count ([] : List Nat)).set! (count - 1) [0]
  expect ((dataClassFlags classes metadata []).all (! ·)) "metadata barrier propagates through a large cycle"
  expect ((dataClassFlags classes closedMetadata (List.range count)).all (! ·)) "many private seeds remain linear"
  IO.println s!"PASS {count}-class reverse graph queue ({(← IO.monoMsNow)-startedGraph}ms)"
  IO.println s!"PASS {count}-element nested literal data/reference scans ({(← IO.monoMsNow) - started}ms)"

def main (args : List String) : IO Unit :=
  if args.contains "--scale" then scale else do
    models
    strictDataModels
