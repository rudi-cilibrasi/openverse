/- Elaboration of a program's signatures (phases 10–12 of `elabProgramCore`); public
   declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Classes

namespace OpenVerse.Front
open OpenVerse

/-- The functions and constants of a program and their signatures, with the
    types of unannotated constants and the effects that are inferred known. -/
structure Signatures where
  /-- The functions and constants, by index (each overload a function of its
      own, `F$ovN`, #74). -/
  tops : List STop
  /-- The generic functions (those with a `where` clause), numbered after `tops`. -/
  generics : List STop
  /-- The signatures of `tops`, by index. -/
  sigs : Array Sig
  /-- The signatures of `generics`, over their type parameters. -/
  gsigs : Array Sig
  /-- The program calls are elaborated against (`Ctx.sigProg`), for what a call
      can do (`Expr.mayFail`, `Expr.writesHeap`): `sigs`, then the generic
      functions' signatures as declared, before the effects of their `block:`s
      and bridges are inferred. -/
  prog : Prog

/-- Every signature: the functions' and constants', then the generic functions'. -/
def Signatures.all (s : Signatures) : List Sig := s.sigs.toList ++ s.gsigs.toList

/-- The signature checks, a phase of `elabProgramCore`: the overloads of a
    function take parameters no call fits two of (Book of Verse ch. 6), and so
    do the overloads of a method a class sees (#106); an override has the
    signature of the method it overrides, is `<suspends>` as it is and allows
    no effect it does not (ch. 10); the implementation a concrete class uses
    has the signature of every declaration of the method above it, also at the
    declaring class's type arguments (#39, #53, #142, #351); an overriding field
    has the inherited field's type; and, last, no field has two interfaces'
    defaults (`Fields.defaultClashes`). -/
def checkSignatures (env : TyEnv) (sigs : Signatures) (cdefs : List CDef) (fields : Fields)
    (methods : Methods) : Except String Unit := do
  let allSigs := sigs.all
  -- overloads take parameters no call fits both of (Book of Verse ch. 6)
  let sigNamed (s : Sig) : List (String × Bool × Ty) :=
    let npos := s.params.length - s.named.length
    (s.named.zip (s.params.drop npos)).map fun ((n, d), t) => (n, d.isSome, t)
  let sigsDistinct (sa sb : Sig) : Bool :=
    let pa := sa.params.take (sa.params.length - sa.named.length)
    let pb := sb.params.take (sb.params.length - sb.named.length)
    let ba := sa.bounds.map fun bound => (bound.base, bound.derived)
    let bb := sb.bounds.map fun bound => (bound.base, bound.derived)
    env.paramsDistinct pa pb ba bb || env.namedDistinct (sigNamed sa) (sigNamed sb) ba bb
  for (n, ms) in env.overloads do
    for (a, i) in ms.zip (List.range ms.length) do
      for b in ms.take i do
        match allSigs.find? (·.name == a), allSigs.find? (·.name == b) with
        | some sa, some sb =>
          if !sigsDistinct sa sb then
            let pos := ((sigs.tops ++ sigs.generics).findSome? fun | .fn q m .. => if m == a then some q else none | _ => none).getD { line := 0, col := 0 }
            let sh (s : Sig) := ", ".intercalate ((s.params.zip (List.range s.params.length)).map fun (t, i) =>
              let npos := s.params.length - s.named.length
              if i < npos then t.show else s!"?{((s.named.drop (i - npos)).head?.map (·.1)).getD "?"}:{t.show}")
            throw s!"{pos.show}: {n} is defined twice with parameters a call cannot tell apart, ({sh sb}) and ({sh sa}): overloads must take disjoint types"
        | _, _ => pure ()
  -- the overloads of a method a class sees take parameters no call fits two
  -- of (#106: a subclass's new overload too; an override has its method's)
  for c in env.classes do
    let classArgs := ((env.sparams.lookup c).getD []).map fun (v, k) => Ty.param v k
    let receiverBounds := ((env.sbounds.lookup c).getD []).map fun (base, derived) =>
      SubtypeEvidence.Bound.mk base derived
    let methodDomain (owner : String) (sg : Sig) : Sig :=
      let formals := (env.sparams.lookup owner).getD []
      -- Receiver formals share this class's scope. Method formals belong
      -- to the inherited declaration and must not capture those names.
      let own := sg.tparams.drop formals.length
      let renames := own.zipIdx.map fun ((v, k), i) =>
        (v, Ty.param s!"$overloadDomain{sg.idx}_{i}" k)
      let σ := (formals.map (·.1)).zip (env.upArgs c classArgs owner) ++ renames
      { sg with
        params := (sg.params.drop 1).map (·.subst σ)
        bounds := sg.bounds.map (·.subst σ) ++ receiverBounds }
    for (mn, ms) in env.methodOverloads do
      let vis : List (String × Sig) := ms.filterMap fun o =>
        ((env.supers c).find? fun e => allSigs.any (·.name == s!"{e}.{o}")).bind fun e =>
          (allSigs.find? (·.name == s!"{e}.{o}")).map fun sg => (s!"{e}.{o}", methodDomain e sg)
      for ((a, sa), i) in vis.zip (List.range vis.length) do
        for (b, sb) in vis.take i do
          if !sigsDistinct sa sb then
            let sh (s : Sig) := ", ".intercalate (s.params.map Ty.show)
            let owner (x : String) := (x.splitOn ".").head!
            let cp := ((cdefs.find? (·.name == c)).map (·.pos)).getD { line := 0, col := 0 }
            throw s!"{cp.show}: {c} has overloads of {mn} a call cannot tell apart, ({sh sb}) in {owner b} and ({sh sa}) in {owner a}: overloads must take disjoint types (an override has the same parameters as its method)"
  -- an override has the signature of the method it overrides, and an
  -- overriding field the inherited field's type (Book of Verse ch. 10)
  -- an override may return a class below the declared one (covariant results)
  let retBelow (a b : Ty) : Bool := a == b || match a, b with
    | .struct S as, .struct T bs => env.classes.contains S && env.classes.contains T && env.isSub S T &&
        env.upArgs S as T == bs
    | _, _ => false
  -- the two methods' types as an instance of class `c` sees them: each
  -- class's type parameters at its type arguments there (#39)
  let inC (c e : String) (t : Ty) : Ty :=
    let cps := ((env.sparams.lookup c).getD []).map fun (v, k) => Ty.param v k
    t.subst ((((env.sparams.lookup e).getD []).map (·.1)).zip (env.upArgs c cps e))
  let clsOf (n : String) : String := (n.splitOn ".").head!
  let sameSigIn (c : String) (a b : Sig) : Bool :=
    let ea := clsOf a.name
    let eb := clsOf b.name
    -- the methods' own type parameters, after their classes', renamed to the
    -- declaration's (and declared comparable alike)
    let own (sg : Sig) (cls : String) := sg.tparams.drop ((env.sparams.lookup cls).getD []).length
    let (oa, ob) := (own a ea, own b eb)
    -- (renamed apart first, so that a class's type arguments, mapped into
    -- `c`'s, cannot capture them)
    let apart (os : List (String × Bool)) : List (String × Ty) :=
      (os.zip (List.range os.length)).map fun ((x, k), i) => (x, Ty.param s!"$o{i}" k)
    let inA (t : Ty) : Ty := inC c ea (t.subst (apart oa))
    let inB (t : Ty) : Ty := inC c eb (t.subst (apart ob))
    let boundsA := (a.methodBounds ((env.sparams.lookup ea).getD []).length).map fun bound =>
      ({ base := inA bound.base, derived := inA bound.derived } : SubtypeEvidence.Bound)
    let boundsB := (b.methodBounds ((env.sparams.lookup eb).getD []).length).map fun bound =>
      ({ base := inB bound.base, derived := inB bound.derived } : SubtypeEvidence.Bound)
    oa.length == ob.length && (oa.map (·.2)) == (ob.map (·.2)) &&
    boundsA.length == boundsB.length && boundsA.all boundsB.contains && boundsB.all boundsA.contains &&
    a.typeValues == b.typeValues &&
    ((a.params.drop 1).map inA) == ((b.params.drop 1).map inB) &&
      retBelow (inA a.ret) (inB b.ret) && a.decides == b.decides &&
      a.named.map (·.1) == b.named.map (·.1)
  -- an implementation has no heap effect its declaration does not allow
  let fxOver (a b : Sig) : Option String := a.fx.find? (!b.fx.contains ·)
  for (mp, mine, theirs) in methods.overridePairs do
    match allSigs.find? (·.name == mine), allSigs.find? (·.name == theirs) with
    | some a, some b =>
      if !sameSigIn (clsOf mine) a b then throw s!"{mp.show}: {mine} must have the signature of {theirs}, which it overrides"
      if a.suspends != b.suspends then
        throw s!"{mp.show}: {mine} must {if b.suspends then "be" else "not be"} <suspends>, as {theirs}, which it overrides, is{if b.suspends then "" else " not"} (#156)"
      if let some k := fxOver a b then
        throw s!"{mp.show}: {mine} allows the effect <{k}>, which {theirs}, which it overrides, does not"
    | _, _ => pure ()
  -- the implementation a concrete class uses has the signature of every
  -- declaration of the method above it
  for (cp, c, impl, decl) in methods.implChecks do
    -- code generic over the declaring class or interface calls `c`'s
    -- implementation only at its own type arguments (#39, #53)
    -- (judged at the class that holds the implementation, whose Verse Core
    -- type arguments must be the declaring one's, and with the same
    -- signature at those type arguments)
    let q := clsOf decl
    let e := clsOf impl
    let atCore (cls : String) (sg : Sig) : List VTy × VTy :=
      let cenv := { env with tvars := env.coreVars cls }
      ((sg.params.drop 1).map (·.toVTy cenv), sg.ret.toVTy cenv)
    -- (at the type arguments `e` fixes, #142, the declaration's types are
    -- taken at the fixed ones)
    let pinσ : Nat → VTy := fun j => match (env.lowerPins (env.pinsOf e))[j]? with
      | some (some t) => t
      | _ => .var j
    -- (#351) at a class an interface sees through a view, the declaration's
    -- types are taken at the view: its type arguments over the class's
    let viewσ : Nat → VTy := if !env.viewed.contains q then pinσ else
      let X := (List.range (env.coreVars e).length).map fun j => Ty.param (pinArg j) false
      let vw := (env.viewOf q e X).map (Ty.toVTy { env with tvars := X.zipIdx.map fun (x, j) => (pinArg j, x) })
      -- (and at the type arguments `e` fixes, as `pinσ`)
      fun j => (vw.getD j (.var j)).subst pinσ
    let sigOk : Bool := match allSigs.find? (·.name == impl), allSigs.find? (·.name == decl) with
      | some a, some b =>
        let ca := atCore e a
        let cb := atCore q b
        ca.1 == cb.1.map (VTy.subst viewσ) && VTy.sub ca.2 (cb.2.subst viewσ)
      | _, _ => true
    match allSigs.find? (·.name == impl), allSigs.find? (·.name == decl) with
    | some a, some b =>
      if !sameSigIn c a b then
        throw s!"{cp.show}: in {c}, {impl} does not have the signature of {decl}"
      if let some k := fxOver a b then
        throw s!"{cp.show}: in {c}, {impl} allows the effect <{k}>, which {decl} does not"
    | _, _ => pure ()
    if !env.viewed.contains q && !env.sameCorePinned e q then
      throw s!"{cp.show}: {c} uses {impl} for {decl}, but {e} has type parameters that {q} does not have, so code generic over {q} could not give them (#39)"
    if !sigOk then
      throw s!"{cp.show}: {c} uses {impl} for {decl}, but their types differ at {q}'s type arguments (as code generic over {q} sees them), so it could not call it (#53)"
  for (fp, cname, f, sty) in fields.overrides do
    let cenv := { env with
      tvars := ((env.sparams.lookup cname).getD []).map fun (v, c) => (v, Ty.param v c)
      boundFacts := (env.sbounds.lookup cname).getD [] }
    let (t, _) ← (resolveTy cenv fp sty).run {}
    match fieldIndex (env.fields cname) f with
    | some (_, t0) =>
      if !(t == t0) then
        throw s!"{fp.show}: field '{f}' of {cname} must have the type it inherits, {t0.show}, not {t.show}"
    | none => pure ()
  if let some msg := fields.defaultClashes[0]? then throw msg

end OpenVerse.Front
