import OpenVerse.Core.Float
/-
  OpenVerse — values of Verse Core.

  Verse values are immutable. Strings are arrays of `char` (UTF-8 code units),
  exactly as in Verse, where `string` is an alias of `[]char`. Options are
  represented by the two constructors `none` (written `false` in Verse) and
  `some`.

  `int` is Verse's 64-bit signed integer. Values of `int` always lie in
  [`Int64.minV`, `Int64.maxV`]; an operation whose mathematical result lies
  outside is a runtime error (`ErrKind.overflow`), never a wrap-around.
-/
namespace OpenVerse

/-- Smallest Verse `int`. -/
def Int64.minV : Int := -9223372036854775808
/-- Largest Verse `int`. -/
def Int64.maxV : Int := 9223372036854775807

/-- `i` is representable as a Verse `int`. -/
def Int64.inRange (i : Int) : Bool := decide (Int64.minV ≤ i) && decide (i ≤ Int64.maxV)

inductive Value where
  /-- `int`; invariant (not enforced by the type): `Int64.inRange i`. -/
  | int   : Int → Value
  /-- `logic`: `true` / `false`. -/
  | logic : Bool → Value
  /-- `char`: one UTF-8 code unit, `0 ≤ c < 256`. -/
  | char  : Nat → Value
  /-- `float` (#127): the bits of an IEEE 64-bit float, canonical (one NaN,
      no negative zero: `Float.canon`), so that equality of values is Verse's
      equality of floats. -/
  | float : UInt64 → Value
  /-- `[]t`, including `string = []char`. An `Array`, so that the
      reference interpreter indexes in constant time (#110); proofs reason
      about its `toList`. -/
  | arr   : Array Value → Value
  /-- `tuple(t₁, …, tₙ)`; `tup []` is the value of `void`. -/
  | tup   : List Value → Value
  /-- The empty option, written `false` in Verse. -/
  | none  : Value
  /-- `option{v}`. -/
  | some  : Value → Value
  /-- A reference to object `a` of the heap (a class instance, #20). -/
  | ref   : Nat → Value
  deriving Repr, Inhabited

namespace Value

/-- The unit value returned by `void` expressions. -/
def void : Value := .tup []

/-- The shared empty array, also used for empty maps and strings. -/
def emptyArray : Value := .arr #[]

/-- Construct an array value. Compiled code shares the empty wrapper. -/
def ofArray (xs : Array Value) : Value := .arr xs

@[simp] theorem ofArray_eq_arr (xs : Array Value) : ofArray xs = .arr xs := rfl

private def ofArrayCached (xs : Array Value) : Value :=
  if xs.isEmpty then emptyArray else .arr xs

@[csimp] private theorem ofArray_eq_ofArrayCached : @ofArray = @ofArrayCached := by
  funext xs
  by_cases h : xs.isEmpty
  · have hx := Array.empty_of_isEmpty h
    subst xs
    rfl
  · simp [ofArray, ofArrayCached, h]

/-- Construct a tuple value. Compiled code shares `void` for the empty tuple. -/
def ofTuple (vs : List Value) : Value := .tup vs

@[simp] theorem ofTuple_eq_tup (vs : List Value) : ofTuple vs = .tup vs := rfl

private def ofTupleCached : List Value → Value
  | [] => void
  | vs => .tup vs

@[csimp] private theorem ofTuple_eq_ofTupleCached : @ofTuple = @ofTupleCached := by
  funext vs
  cases vs <;> rfl

/-- Construct an integer value. Compiled code shares the wrappers for 0..1025. -/
def ofInt (i : Int) : Value := .int i

@[simp] theorem ofInt_eq_int (i : Int) : ofInt i = .int i := rfl

private def smallInts : Array Value :=
  Array.ofFn fun i : Fin 1026 => .int (i.val : Int)

private def ofIntCached : Int → Value
  | .ofNat n =>
    if h : n < 1026 then smallInts[n]'(by simpa [smallInts] using h)
    else .int (.ofNat n)
  | .negSucc n => .int (.negSucc n)

/-- Pooling changes physical sharing only, including at the cache boundaries. -/
@[csimp] private theorem ofInt_eq_ofIntCached : @ofInt = @ofIntCached := by
  funext i
  cases i with
  | ofNat n =>
    by_cases h : n < 1026 <;> simp [ofInt, ofIntCached, smallInts, h]
  | negSucc n => rfl

/-- Build a Verse string from a Lean string (UTF-8 bytes). -/
def ofString (s : String) : Value := ofArray (s.toUTF8.toList.map fun b => .char b.toNat).toArray

mutual
/-- Decidable equality, written by hand: Lean cannot derive it for a nested inductive. -/
def decEq : (a b : Value) → Decidable (a = b)
  | .int x, .int y =>
    if h : x = y then isTrue (by subst h; rfl) else isFalse (by intro h'; cases h'; exact h rfl)
  | .logic x, .logic y =>
    if h : x = y then isTrue (by subst h; rfl) else isFalse (by intro h'; cases h'; exact h rfl)
  | .char x, .char y =>
    if h : x = y then isTrue (by subst h; rfl) else isFalse (by intro h'; cases h'; exact h rfl)
  | .float x, .float y =>
    if h : x = y then isTrue (by subst h; rfl) else isFalse (by intro h'; cases h'; exact h rfl)
  | .arr a, .arr b =>
    -- (the sizes first, in constant time: arrays of different lengths are
    -- told apart without walking them)
    if hl : a.size = b.size then
      match decEqList a.toList b.toList with
      | isTrue h => isTrue (congrArg Value.arr (Array.toList_inj.mp h))
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    else isFalse (by intro h'; cases h'; exact hl rfl)
  | .tup xs, .tup ys => match decEqList xs ys with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .none, .none => isTrue rfl
  | .some x, .some y => match decEq x y with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .ref x, .ref y =>
    if h : x = y then isTrue (by subst h; rfl) else isFalse (by intro h'; cases h'; exact h rfl)
  | .int _, .ref _ | .logic _, .ref _ | .char _, .ref _ | .arr _, .ref _ | .tup _, .ref _ | .none, .ref _
  | .some _, .ref _ => isFalse (by intro h; cases h)
  | .ref _, .int _ | .ref _, .logic _ | .ref _, .char _ | .ref _, .arr _ | .ref _, .tup _ | .ref _, .none
  | .ref _, .some _ => isFalse (by intro h; cases h)
  | .int _, .logic _ | .int _, .char _ | .int _, .arr _ | .int _, .tup _ | .int _, .none | .int _, .some _ => isFalse (by intro h; cases h)
  | .logic _, .int _ | .logic _, .char _ | .logic _, .arr _ | .logic _, .tup _ | .logic _, .none | .logic _, .some _ => isFalse (by intro h; cases h)
  | .char _, .int _ | .char _, .logic _ | .char _, .arr _ | .char _, .tup _ | .char _, .none | .char _, .some _ => isFalse (by intro h; cases h)
  | .arr _, .int _ | .arr _, .logic _ | .arr _, .char _ | .arr _, .tup _ | .arr _, .none | .arr _, .some _ => isFalse (by intro h; cases h)
  | .tup _, .int _ | .tup _, .logic _ | .tup _, .char _ | .tup _, .arr _ | .tup _, .none | .tup _, .some _ => isFalse (by intro h; cases h)
  | .none, .int _ | .none, .logic _ | .none, .char _ | .none, .arr _ | .none, .tup _ | .none, .some _ => isFalse (by intro h; cases h)
  | .some _, .int _ | .some _, .logic _ | .some _, .char _ | .some _, .arr _ | .some _, .tup _ | .some _, .none => isFalse (by intro h; cases h)
  | .float _, .int _ | .float _, .logic _ | .float _, .char _ | .float _, .arr _ | .float _, .tup _
  | .float _, .none | .float _, .some _ | .float _, .ref _
  | .int _, .float _ | .logic _, .float _ | .char _, .float _ | .arr _, .float _ | .tup _, .float _
  | .none, .float _ | .some _, .float _ | .ref _, .float _ => isFalse (by intro h; cases h)
def decEqList : (as bs : List Value) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | a :: as, b :: bs => match decEq a b, decEqList as bs with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h1, _ => isFalse (by intro h; cases h; exact h1 rfl)
    | _, isFalse h2 => isFalse (by intro h; cases h; exact h2 rfl)
end

instance : DecidableEq Value := decEq

/-! ### Verse's equality of values (`veq`)

Verse has one empty value, written `false` or `()` (Book of Verse ch. 2,
"void, true, tuple() and false"): it is the logic false, the value of
`void` and `tuple()`, the empty option, and the empty array, string and
map. Verse Core holds it four ways, one per type that has it:
`.logic false`, `.tup []`, `.none` and `.arr #[]`. `veq` is the equality
of Verse: the structural equality of values (`decEq`), except that any two
of those four are equal, at every depth (`array{false} = array{()}`).
`veq_iff` characterizes it: two values are `veq` exactly when they are
equal once every empty value in them is made `()` (`norm`); so it is an
equivalence (`veq_refl`, `veq_comm`, `veq_trans`) and a congruence for the
constructors that hold values (`veq_some`, `veq_tup_of_get`,
`veq_arr_of_get`). On two values of one type without `dyn` it is `=`
(`veq_iff_eq_of_hasTy`, `Typing.lean`): each type holds the empty value one
way. -/

/-- The empty value of Verse (`false`, `()`, the empty option, array, string
    and map, Book of Verse ch. 2), as Verse Core holds it at each type:
    `.logic false`, `.tup []`, `.none`, `.arr #[]`. -/
def isEmpty : Value → Bool
  | .logic false | .tup [] | .none => true
  | .arr a => a.isEmpty
  | _ => false

mutual
/-- Verse's equality of values: structural, except that any two of the
    four representations of the empty value are equal, at every depth. -/
def veq : Value → Value → Bool
  | .int x, .int y => x == y
  | .logic x, .logic y => x == y
  | .char x, .char y => x == y
  | .float x, .float y => x == y
  | .arr a, .arr b => a.size == b.size && veqList a.toList b.toList
  | .tup xs, .tup ys => veqList xs ys
  | .none, .none => true
  | .some x, .some y => veq x y
  | .ref x, .ref y => x == y
  | a, b => a.isEmpty && b.isEmpty
/-- `veq`, element by element, of two lists of the same length. -/
def veqList : List Value → List Value → Bool
  | [], [] => true
  | a :: as, b :: bs => veq a b && veqList as bs
  | _, _ => false
end

mutual
/-- `v` with each empty value, at every depth, made `()`. -/
def norm : Value → Value
  | .logic false => void
  | .none => void
  | .arr ⟨[]⟩ => void
  | .arr ⟨v :: vs⟩ => .arr ⟨normList (v :: vs)⟩
  | .tup vs => .tup (normList vs)
  | .some v => .some (norm v)
  | v => v
def normList : List Value → List Value
  | [] => []
  | v :: vs => norm v :: normList vs
end

theorem normList_length : ∀ (vs : List Value), (normList vs).length = vs.length
  | [] => rfl
  | _ :: vs => by simp [normList, normList_length vs]

theorem norm_eq_void_iff (v : Value) : norm v = void ↔ v.isEmpty = true := by
  match v with
  | .int _ => simp [norm, isEmpty, void]
  | .logic b => cases b <;> simp [norm, isEmpty, void]
  | .char _ => simp [norm, isEmpty, void]
  | .float _ => simp [norm, isEmpty, void]
  | .arr ⟨[]⟩ => simp [norm, isEmpty, void]
  | .arr ⟨_ :: _⟩ => simp [norm, isEmpty, void]
  | .tup [] => simp [norm, normList, isEmpty, void]
  | .tup (_ :: _) => simp [norm, normList, isEmpty, void]
  | .none => simp [norm, isEmpty, void]
  | .some _ => simp [norm, isEmpty, void]
  | .ref _ => simp [norm, isEmpty, void]

/-- The constructor of a value. -/
def kind : Value → Nat
  | .int _ => 0 | .logic _ => 1 | .char _ => 2 | .float _ => 3 | .arr _ => 4
  | .tup _ => 5 | .none => 6 | .some _ => 7 | .ref _ => 8

/-- A value that is not empty keeps its constructor under `norm`. -/
theorem kind_norm (v : Value) (h : v.isEmpty = false) : kind (norm v) = kind v := by
  match v with
  | .int _ => simp [norm]
  | .logic b => cases b <;> simp_all [norm, isEmpty]
  | .char _ => simp [norm]
  | .float _ => simp [norm]
  | .arr ⟨[]⟩ => simp [isEmpty] at h
  | .arr ⟨_ :: _⟩ => simp [norm, kind]
  | .tup _ => simp [norm, kind]
  | .none => simp [isEmpty] at h
  | .some _ => simp [norm, kind]
  | .ref _ => simp [norm]

/-- Values of different constructors are `veq` exactly when both are empty,
    and `norm` makes them equal exactly then. -/
theorem veq_cross (a b : Value) (hk : kind a ≠ kind b) : veq a b = true ↔ norm a = norm b := by
  have hv : veq a b = (a.isEmpty && b.isEmpty) := by
    cases a <;> cases b <;> simp_all [kind, veq]
  rw [hv]
  cases ha : a.isEmpty <;> cases hb : b.isEmpty
  · simp only [Bool.and_self, Bool.false_eq_true, false_iff]
    intro h; exact hk (by rw [← kind_norm a ha, ← kind_norm b hb, h])
  · simp only [Bool.false_and, Bool.false_eq_true, false_iff]
    rw [(norm_eq_void_iff b).mpr hb]; intro h
    have := (norm_eq_void_iff a).mp h; simp_all
  · simp only [Bool.and_false, Bool.false_eq_true, false_iff]
    rw [(norm_eq_void_iff a).mpr ha]; intro h
    have := (norm_eq_void_iff b).mp h.symm; simp_all
  · simp only [Bool.and_self, true_iff]
    rw [(norm_eq_void_iff a).mpr ha, (norm_eq_void_iff b).mpr hb]

mutual
theorem veq_iff : ∀ (a b : Value), veq a b = true ↔ norm a = norm b
  | .int x, .int y => by simp [veq, norm]
  | .logic x, .logic y => by cases x <;> cases y <;> simp [veq, norm, void]
  | .char x, .char y => by simp [veq, norm]
  | .float x, .float y => by simp [veq, norm]
  | .arr ⟨xs⟩, .arr ⟨ys⟩ => by
    have ih := veqList_iff xs ys
    cases xs with
    | nil => cases ys with
      | nil => simp [veq, veqList, norm]
      | cons y ys => simp [veq, norm, normList, void]
    | cons x xs => cases ys with
      | nil => simp [veq, norm, normList, void]
      | cons y ys =>
        simp only [veq, norm, Array.size, List.length_cons, Bool.and_eq_true, beq_iff_eq,
          Value.arr.injEq, Array.mk.injEq]
        constructor
        · intro ⟨_, h⟩; exact ih.mp h
        · intro h
          refine ⟨?_, ih.mpr h⟩
          have := congrArg List.length h
          simpa [normList_length] using this
  | .tup xs, .tup ys => by
    have ih := veqList_iff xs ys
    simp only [veq, norm, Value.tup.injEq]; exact ih
  | .none, .none => by simp [veq, norm]
  | .some x, .some y => by
    have ih := veq_iff x y
    simp only [veq, norm, Value.some.injEq]; exact ih
  | .ref x, .ref y => by simp [veq, norm]
  | .int _, .logic _ | .int _, .char _ | .int _, .float _ | .int _, .arr _
  | .int _, .tup _ | .int _, .none | .int _, .some _ | .int _, .ref _
  | .logic _, .int _ | .logic _, .char _ | .logic _, .float _ | .logic _, .arr _
  | .logic _, .tup _ | .logic _, .none | .logic _, .some _ | .logic _, .ref _
  | .char _, .int _ | .char _, .logic _ | .char _, .float _ | .char _, .arr _
  | .char _, .tup _ | .char _, .none | .char _, .some _ | .char _, .ref _
  | .float _, .int _ | .float _, .logic _ | .float _, .char _ | .float _, .arr _
  | .float _, .tup _ | .float _, .none | .float _, .some _ | .float _, .ref _
  | .arr _, .int _ | .arr _, .logic _ | .arr _, .char _ | .arr _, .float _
  | .arr _, .tup _ | .arr _, .none | .arr _, .some _ | .arr _, .ref _
  | .tup _, .int _ | .tup _, .logic _ | .tup _, .char _ | .tup _, .float _
  | .tup _, .arr _ | .tup _, .none | .tup _, .some _ | .tup _, .ref _
  | .none, .int _ | .none, .logic _ | .none, .char _ | .none, .float _
  | .none, .arr _ | .none, .tup _ | .none, .some _ | .none, .ref _
  | .some _, .int _ | .some _, .logic _ | .some _, .char _ | .some _, .float _
  | .some _, .arr _ | .some _, .tup _ | .some _, .none | .some _, .ref _
  | .ref _, .int _ | .ref _, .logic _ | .ref _, .char _ | .ref _, .float _
  | .ref _, .arr _ | .ref _, .tup _ | .ref _, .none | .ref _, .some _ =>
    veq_cross _ _ (by simp [kind])
theorem veqList_iff : ∀ (xs ys : List Value), veqList xs ys = true ↔ normList xs = normList ys
  | [], [] => by simp [veqList, normList]
  | [], _ :: _ => by simp [veqList, normList]
  | _ :: _, [] => by simp [veqList, normList]
  | x :: xs, y :: ys => by
    have h1 := veq_iff x y
    have h2 := veqList_iff xs ys
    simp only [veqList, normList, Bool.and_eq_true, List.cons.injEq]
    rw [h1, h2]
end

/-- `veq` is reflexive. -/
theorem veq_refl (a : Value) : veq a a = true := (veq_iff a a).mpr rfl

/-- `veq` is symmetric. -/
theorem veq_comm (a b : Value) : veq a b = veq b a := by
  cases h : veq b a
  · cases h' : veq a b
    · rfl
    · have := (veq_iff a b).mp h'
      have := (veq_iff b a).mpr this.symm
      simp_all
  · exact (veq_iff a b).mpr ((veq_iff b a).mp h).symm

/-- `veq` is transitive. -/
theorem veq_trans {a b c : Value} (h1 : veq a b = true) (h2 : veq b c = true) : veq a c = true :=
  (veq_iff a c).mpr (((veq_iff a b).mp h1).trans ((veq_iff b c).mp h2))

/-- Equal values are `veq`. -/
theorem veq_of_eq {a b : Value} (h : a = b) : veq a b = true := h ▸ veq_refl a

/-- Any two empty values are `veq`: `false`, `()`, the empty option, array,
    string and map are one value. -/
theorem veq_of_isEmpty {a b : Value} (ha : a.isEmpty = true) (hb : b.isEmpty = true) :
    veq a b = true :=
  (veq_iff a b).mpr (((norm_eq_void_iff a).mpr ha).trans ((norm_eq_void_iff b).mpr hb).symm)

/-- A value `veq` to an empty value is empty. -/
theorem isEmpty_of_veq {a b : Value} (h : veq a b = true) (ha : a.isEmpty = true) :
    b.isEmpty = true :=
  (norm_eq_void_iff b).mp (((veq_iff a b).mp h).symm.trans ((norm_eq_void_iff a).mpr ha))

/-- `veqList` is `veq` element by element, on lists of one length. -/
theorem veqList_iff_get : ∀ (xs ys : List Value),
    veqList xs ys = true ↔ xs.length = ys.length ∧
      ∀ (i : Nat) (hx : i < xs.length) (hy : i < ys.length), veq xs[i] ys[i] = true
  | [], [] => by simp [veqList]
  | [], _ :: _ => by simp [veqList]
  | _ :: _, [] => by simp [veqList]
  | x :: xs, y :: ys => by
    simp only [veqList, Bool.and_eq_true, List.length_cons, Nat.add_right_cancel_iff]
    rw [veqList_iff_get xs ys]
    constructor
    · rintro ⟨h0, hl, hs⟩
      refine ⟨hl, fun i hx hy => ?_⟩
      cases i with
      | zero => exact h0
      | succ i => exact hs i (by simpa using hx) (by simpa using hy)
    · rintro ⟨hl, hs⟩
      exact ⟨hs 0 (by simp) (by simp), hl,
        fun i hx hy => hs (i + 1) (by simpa using hx) (by simpa using hy)⟩

/-- Congruence: options of `veq` values are `veq`. -/
theorem veq_some (x y : Value) : veq (.some x) (.some y) = veq x y := rfl

/-- Congruence: tuples of `veq` values, element by element, are `veq`. -/
theorem veq_tup_of_get {xs ys : List Value} (hl : xs.length = ys.length)
    (h : ∀ (i : Nat) (hx : i < xs.length) (hy : i < ys.length), veq xs[i] ys[i] = true) :
    veq (.tup xs) (.tup ys) = true := by
  simp only [veq]; exact (veqList_iff_get xs ys).mpr ⟨hl, h⟩

/-- Congruence: arrays of `veq` values, element by element, are `veq`. -/
theorem veq_arr_of_get {xs ys : List Value} (hl : xs.length = ys.length)
    (h : ∀ (i : Nat) (hx : i < xs.length) (hy : i < ys.length), veq xs[i] ys[i] = true) :
    veq (.arr ⟨xs⟩) (.arr ⟨ys⟩) = true := by
  simp only [veq, Bool.and_eq_true, beq_iff_eq]
  exact ⟨by simpa using hl, (veqList_iff_get xs ys).mpr ⟨hl, h⟩⟩

/-- A value `veq` to an int is that int. -/
theorem veq_int_right (v : Value) (j : Int) : veq v (.int j) = decide (v = .int j) := by
  cases v with
  | int a => by_cases h : a = j <;> simp [veq, h]
  | _ => simp [veq, isEmpty]

/-- `array{false} = array{()}`: one empty value inside an array, held two ways. -/
theorem veq_example : veq (.arr #[.logic false]) (.arr #[.tup []]) = true := by decide


/-- Render a value the way the reference implementation prints it (`ToString`). -/
partial def render : Value → String
  | .int i => toString i
  | .logic b => if b then "true" else "false"
  | .char c => String.singleton (Char.ofNat c)
  | .float b => VFloat.render b
  | .arr vs =>
    if vs.all (fun v => match v with | .char _ => true | _ => false) && !vs.isEmpty then
      String.fromUTF8! (ByteArray.mk (vs.map (fun v => match v with
        | .char c => c.toUInt8 | _ => 0)))
    else "array{" ++ ", ".intercalate (vs.toList.map render) ++ "}"
  | .tup vs => "(" ++ ", ".intercalate (vs.map render) ++ ")"
  | .none => "false"
  | .some v => "option{" ++ render v ++ "}"
  | .ref a => s!"ref {a}"

end Value

/-- Runtime errors. They end the whole program; failure contexts do not catch them. -/
inductive ErrKind where
  /-- An `int` result outside the 64-bit range. -/
  | overflow
  /-- An operation applied to values of the wrong shape (excluded by the type checker). -/
  | type
  /-- A slot index outside the current frame (excluded by the loader / elaborator). -/
  | slot
  /-- A call to a function that does not exist or with the wrong number of arguments. -/
  | call
  /-- `break` outside `loop`, or `return` reaching a place it cannot. -/
  | control
  /-- An explicit `Err()` call. -/
  | user
  deriving Repr, DecidableEq, Inhabited

/-- The outcome of evaluating one expression. -/
inductive Res where
  /-- Success with a value. -/
  | ok   : Value → Res
  /-- Verse failure: caught by the nearest failure context, which rolls back. -/
  | fail : Res
  /-- `break` travelling to the nearest `loop`. -/
  | brk  : Res
  /-- `return v` travelling to the function boundary. -/
  | ret  : Value → Res
  /-- A runtime error: ends the program. -/
  | err  : ErrKind → Res
  deriving Repr, DecidableEq, Inhabited

namespace Res
/-- Is this the normal (successful) outcome? -/
def isOk : Res → Bool
  | .ok _ => true
  | _ => false

@[simp] theorem isOk_ok (v : Value) : (Res.ok v).isOk = true := rfl
@[simp] theorem isOk_fail : Res.fail.isOk = false := rfl
@[simp] theorem isOk_brk : Res.brk.isOk = false := rfl
@[simp] theorem isOk_ret (v : Value) : (Res.ret v).isOk = false := rfl
@[simp] theorem isOk_err (e : ErrKind) : (Res.err e).isOk = false := rfl

/-- Range-checked `int` result. -/
def ofInt (i : Int) : Res := if Int64.inRange i then .ok (Value.ofInt i) else .err .overflow
end Res

/-- The outcome of evaluating a list of expressions left to right. -/
inductive LRes where
  | ok   : List Value → LRes
  /-- The first abrupt (non-`ok`) outcome; never `Res.ok`. -/
  | stop : Res → LRes
  deriving Repr, DecidableEq, Inhabited

end OpenVerse
