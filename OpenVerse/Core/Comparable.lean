/-
  OpenVerse — `comparable` in Verse Core: the box of a comparable value.

  A value of Verse's `comparable` (Book of Verse ch. 11, "Comparable and
  Equality") is a value of any comparable type, and `=` on two of them holds
  exactly when they have the same type and are equal: `0 = 0.0` fails, an
  enum's value never equals another enum's or an int. Verse Core holds
  several Verse types alike (an enum's value is its index, an `int`; a
  `char32` an `int`; a struct the tuple of its fields; a rational the tuple
  of its numerator and denominator; a map the array of its pairs), so the
  front end *boxes* a value before it becomes a `comparable` (a `VTy.dyn`):
  it puts a code, an int, where the representation is ambiguous, and makes
  one representation of the values Verse identifies (a tuple and the array
  of its elements, an int and the rational it is). Verse Core's equality
  (`Value.veq`) on boxes is then Verse's.

  `Code` says how a value of a comparable type is boxed, and `Code.box`
  boxes it: this is the specification the front end's boxing code
  implements (`Front/Comparable.lean`). Proved here:

  - `veq_box`: boxing preserves and reflects `veq` on values of one code;
    with `veq_iff_eq_of_hasTy`, `box_veq_iff_eq` (boxes of two values of one
    Verse type are equal exactly when the values are).
  - `box_tag_ne`, `box_plain_tagged`, `box_map_tagged`, `box_rational_tagged`:
    boxes under different codes are never equal, and a tagged box never
    equals the box of a code with no tag.
  - `box_empty_plain`, `box_empty_map`, `box_tuple_array`, `box_rational_int`:
    what Verse identifies stays one value: the empty values (of the codes
    that hold one), a tuple and the array of its elements, an integral
    rational and its int.
  - `box_dyn`: every box is a `dyn` (so converting to `comparable` is
    subsumption).
-/
import OpenVerse.Core.Typing

namespace OpenVerse

/-- How a value of a comparable Verse type is boxed (the codes of a box). -/
inductive Code where
  /-- The value itself, of Verse Core type `t`: an `int`, a `float`, a
      `logic`, a `char`, a refinement, a `<unique>` object, a `comparable`
      (`dyn`), `tuple()`. -/
  | id : VTy → Code
  /-- `tup [int k, box]`: under code `k` (an enum, `int` inside; `char32`,
      code 0; a struct, its `fields`). -/
  | tagged : Nat → Code → Code
  /-- A struct's fields, inside its tag: a tuple of their boxes. -/
  | fields : List Code → Code
  /-- A tuple: the array of its elements' boxes (a tuple is the array of its
      elements, Book of Verse ch. 3). -/
  | tuple : List Code → Code
  | array : Code → Code
  | option : Code → Code
  /-- A map: the empty one as it is; another under code 2, its pairs
      (in order) boxed. -/
  | map : Code → Code → Code
  /-- A rational `(n, d)`: `n` when `d = 1` (an int is the rational it is),
      else under code 1. -/
  | rational
  deriving Repr, Inhabited

namespace Code

mutual
/-- The Verse Core type of the values a code boxes. -/
def vty : Code → VTy
  | .id t => t
  | .tagged _ c => vty c
  | .fields cs | .tuple cs => .tup (vtyL cs)
  | .array c => .arr (vty c)
  | .option c => .opt (vty c)
  | .map k v => .arr (.tup [vty k, vty v])
  | .rational => .tup [.int, .int]
def vtyL : List Code → List VTy
  | [] => []
  | c :: cs => vty c :: vtyL cs
end

/-- A map's pair, boxed. -/
def boxPair (bk bv : Value → Value) : Value → Value
  | .tup [k, w] => .tup [bk k, bv w]
  | p => p

mutual
/-- The box of a value of type `c.vty`. -/
def box : Code → Value → Value
  | .id _, v => v
  | .tagged k c, v => .tup [.int k, box c v]
  | .fields cs, .tup vs => .tup (boxL cs vs)
  | .tuple cs, .tup vs => .arr (boxL cs vs).toArray
  | .array c, .arr vs => .arr ⟨vs.toList.map (box c)⟩
  | .option c, .some v => .some (box c v)
  | .map k w, .arr ps =>
    if ps.toList.isEmpty then .arr ps
    else .tup [.int 2, .arr ⟨ps.toList.map (boxPair (box k) (box w))⟩]
  | .rational, .tup [.int n, .int d] => if d = 1 then .int n else .tup [.int 1, .tup [.int n, .int d]]
  | _, v => v
/-- The boxes of a list of values, one code each. -/
def boxL : List Code → List Value → List Value
  | c :: cs, v :: vs => box c v :: boxL cs vs
  | _, _ => []
end

/-- A code whose boxes carry no code at the top: never `tup [int k, _]`. -/
def plain : Code → Bool
  | .id .dyn => false
  | .id (.tup (_ :: _)) => false
  | .id _ | .tuple _ | .array _ | .option _ => true
  | _ => false

end Code

open Value

/-! ### Every box is a `dyn` -/

theorem box_dyn (V : Variances) (Ξ : HeapTy) (c : Code) (v : Value) : hasTy V Ξ (c.box v) .dyn = true := hasTy_dyn V Ξ _

/-! ### Boxing preserves and reflects `veq` on one code -/

theorem Code.veqList_map_of {f : Value → Value} {P : Value → Prop}
    (hf : ∀ a b, P a → P b → veq (f a) (f b) = veq a b) :
    ∀ (xs ys : List Value), (∀ x ∈ xs, P x) → (∀ y ∈ ys, P y) →
      veqList (xs.map f) (ys.map f) = veqList xs ys
  | [], [], _, _ => rfl
  | [], _ :: _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | x :: xs, y :: ys, hx, hy => by
    simp only [List.map_cons, veqList]
    rw [hf x y (hx x (by simp)) (hy y (by simp)),
      Code.veqList_map_of hf xs ys (fun x' h => hx x' (by simp [h])) (fun y' h => hy y' (by simp [h]))]

theorem Code.allTy_mem {V : Variances} {Ξ : HeapTy} {xs : List Value} {t : VTy} (h : allTy V Ξ xs t = true) :
    ∀ x ∈ xs, hasTy V Ξ x t = true := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    simp only [allTy, Bool.and_eq_true] at h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact ih h.2 x hx

theorem Code.allTys_length {V : Variances} {Ξ : HeapTy} : ∀ {xs : List Value} {ts : List VTy}, allTys V Ξ xs ts = true →
    xs.length = ts.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [allTys, Bool.and_eq_true] at h
    simp [Code.allTys_length h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [allTys] at h

theorem Code.vtyL_length : ∀ (cs : List Code), (Code.vtyL cs).length = cs.length
  | [] => rfl
  | _ :: cs => by simp [Code.vtyL, Code.vtyL_length cs]

theorem Code.boxL_length : ∀ (cs : List Code) (vs : List Value), vs.length = cs.length →
    (Code.boxL cs vs).length = cs.length
  | [], [], _ => rfl
  | _ :: cs, _ :: vs, h => by simp [Code.boxL, Code.boxL_length cs vs (by simpa using h)]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

mutual
/-- **Boxing preserves and reflects Verse's equality on one code**: two
    values of a comparable type have equal boxes exactly when they are
    equal. -/
theorem veq_box (V : Variances) (Ξ : HeapTy) : ∀ (c : Code) (a b : Value), hasTy V Ξ a c.vty = true →
    hasTy V Ξ b c.vty = true → veq (c.box a) (c.box b) = veq a b
  | .id _, _, _, _, _ => rfl
  | .tagged k c, a, b, ha, hb => by
    simp only [Code.box, veq, veqList, beq_self_eq_true, Bool.true_and, Bool.and_true]
    exact veq_box V Ξ c a b ha hb
  | .fields cs, a, b, ha, hb => by
    cases a <;> simp [Code.vty, hasTy] at ha
    cases b <;> simp [Code.vty, hasTy] at hb
    rename_i xs ys
    simp only [Code.box, veq]
    exact veq_boxL V Ξ cs xs ys ha hb
  | .tuple cs, a, b, ha, hb => by
    cases a <;> simp [Code.vty, hasTy] at ha
    cases b <;> simp [Code.vty, hasTy] at hb
    rename_i xs ys
    simp only [Code.box, veq, List.size_toArray]
    rw [veq_boxL V Ξ cs xs ys ha hb,
      Code.boxL_length cs xs (by rw [Code.allTys_length ha, Code.vtyL_length]),
      Code.boxL_length cs ys (by rw [Code.allTys_length hb, Code.vtyL_length])]
    simp
  | .array c, a, b, ha, hb => by
    cases a <;> simp [Code.vty, hasTy] at ha
    cases b <;> simp [Code.vty, hasTy] at hb
    rename_i xs ys
    simp only [Code.box, veq, Array.size, List.length_map]
    rw [Code.veqList_map_of (P := fun v => hasTy V Ξ v c.vty = true) (fun a b ha hb => veq_box V Ξ c a b ha hb)
      xs.toList ys.toList (Code.allTy_mem ha) (Code.allTy_mem hb)]
  | .option c, a, b, ha, hb => by
    cases a <;> simp [Code.vty, hasTy] at ha <;> cases b <;> simp [Code.vty, hasTy] at hb <;>
      simp [Code.box, veq, isEmpty]
    exact veq_box V Ξ c _ _ ha hb
  | .map k w, a, b, ha, hb => by
    cases a <;> simp [Code.vty, hasTy] at ha
    cases b <;> simp [Code.vty, hasTy] at hb
    rename_i xs ys
    have hpair : ∀ p q, hasTy V Ξ p (.tup [k.vty, w.vty]) = true → hasTy V Ξ q (.tup [k.vty, w.vty]) = true →
        veq (Code.boxPair (Code.box k) (Code.box w) p) (Code.boxPair (Code.box k) (Code.box w) q) = veq p q := by
      intro p q hp hq
      cases p <;> simp [hasTy] at hp
      cases q <;> simp [hasTy] at hq
      rename_i ps qs
      rcases ps with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, ps⟩⟩⟩ <;> simp [allTys] at hp
      rcases qs with _ | ⟨q1, _ | ⟨q2, _ | ⟨q3, qs⟩⟩⟩ <;> simp [allTys] at hq
      simp only [Code.boxPair, veq, veqList]
      rw [veq_box V Ξ k p1 q1 hp.1 hq.1, veq_box V Ξ w p2 q2 hp.2 hq.2]
    have hl := Code.veqList_map_of (P := fun v => hasTy V Ξ v (.tup [k.vty, w.vty]) = true) hpair
      xs.toList ys.toList (Code.allTy_mem ha) (Code.allTy_mem hb)
    rcases xs with ⟨_ | ⟨x, xs⟩⟩ <;> rcases ys with ⟨_ | ⟨y, ys⟩⟩ <;>
      simp_all [Code.box, veq, isEmpty, veqList]
  | .rational, a, b, ha, hb => by
    cases a <;> simp [Code.vty, hasTy] at ha
    cases b <;> simp [Code.vty, hasTy] at hb
    rename_i xs ys
    rcases xs with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, xs⟩⟩⟩ <;> simp [allTys] at ha
    rcases ys with _ | ⟨y1, _ | ⟨y2, _ | ⟨y3, ys⟩⟩⟩ <;> simp [allTys] at hb
    have hint : ∀ v : Value, hasTy V Ξ v .int = true → ∃ n, v = .int n := by
      intro v hv; cases v <;> simp_all [hasTy]
    obtain ⟨n, rfl⟩ := hint x1 ha.1
    obtain ⟨d, rfl⟩ := hint x2 ha.2
    obtain ⟨m, rfl⟩ := hint y1 hb.1
    obtain ⟨e, rfl⟩ := hint y2 hb.2
    by_cases hd : d = 1 <;> by_cases he : e = 1 <;> simp [Code.box, veq, veqList, hd, he, isEmpty]
    all_goals omega
theorem veq_boxL (V : Variances) (Ξ : HeapTy) : ∀ (cs : List Code) (xs ys : List Value),
    allTys V Ξ xs (Code.vtyL cs) = true → allTys V Ξ ys (Code.vtyL cs) = true →
    veqList (Code.boxL cs xs) (Code.boxL cs ys) = veqList xs ys
  | [], [], [], _, _ => rfl
  | c :: cs, x :: xs, y :: ys, hx, hy => by
    simp only [Code.vtyL, allTys, Bool.and_eq_true] at hx hy
    simp only [Code.boxL, veqList]
    rw [veq_box V Ξ c x y hx.1 hy.1, veq_boxL V Ξ cs xs ys hx.2 hy.2]
  | [], _ :: _, _, hx, _ | [], _, _ :: _, _, hy => by simp [Code.vtyL, allTys] at *
  | _ :: _, [], _, hx, _ | _ :: _, _, [], _, hy => by simp [Code.vtyL, allTys] at *
end

/-- Boxes of two values of one comparable type are equal exactly when the
    values are (when the type has no `comparable` inside, whose values may
    hold the empty value several ways). -/
theorem box_veq_iff_eq (V : Variances) (Ξ : HeapTy) (c : Code) (a b : Value) (hc : c.vty.dynFree = true)
    (ha : hasTy V Ξ a c.vty = true) (hb : hasTy V Ξ b c.vty = true) :
    veq (c.box a) (c.box b) = true ↔ a = b := by
  rw [veq_box V Ξ c a b ha hb]; exact veq_iff_eq_of_hasTy V Ξ a b c.vty hc ha hb

/-! ### Different codes: never equal -/

/-- Boxes under two different codes are never equal. -/
theorem box_tag_ne {k l : Nat} (hkl : k ≠ l) (c d : Code) (a b : Value) :
    veq ((Code.tagged k c).box a) ((Code.tagged l d).box b) = false := by
  simp [Code.box, veq, veqList]
  intro h; exact absurd (Int.ofNat_inj.mp h) hkl

/-- A tagged box never equals the box of a value of a code with no tag
    (an `int`, a `float`, a `logic`, a `char`, an array, an option, a tuple,
    `tuple()`, a `<unique>` object): an enum's value is no int, a struct no
    tuple. -/
theorem box_plain_tagged (V : Variances) (Ξ : HeapTy) (c : Code) (hc : c.plain = true) (a : Value)
    (ha : hasTy V Ξ a c.vty = true) (k : Nat) (d : Code) (b : Value) :
    veq (c.box a) ((Code.tagged k d).box b) = false := by
  cases c with
  | id t =>
    simp only [Code.vty] at ha
    cases a with
    | tup xs =>
      cases t <;> simp [hasTy, Code.plain] at ha hc
      rename_i ts
      cases ts with
      | nil => cases xs <;> simp_all [allTys, Code.box, veq, veqList]
      | cons _ _ => simp_all
    | _ => simp [Code.box, veq, isEmpty]
  | tuple cs => cases a <;> simp [Code.vty, hasTy] at ha <;> simp [Code.box, veq, isEmpty]
  | array c => cases a <;> simp [Code.vty, hasTy] at ha <;> simp [Code.box, veq, isEmpty]
  | option c => cases a <;> simp [Code.vty, hasTy] at ha <;> simp [Code.box, veq, isEmpty]
  | _ => simp [Code.plain] at hc

/-- A map's box equals a tagged box only under the map's code, 2. -/
theorem box_map_tagged (V : Variances) (Ξ : HeapTy) (ck cv : Code) (a : Value) (ha : hasTy V Ξ a (Code.map ck cv).vty = true)
    (k : Nat) (d : Code) (b : Value)
    (h : veq ((Code.map ck cv).box a) ((Code.tagged k d).box b) = true) : k = 2 := by
  cases a <;> simp [Code.vty, hasTy] at ha
  rename_i xs
  rcases xs with ⟨_ | ⟨x, xs⟩⟩
  · simp [Code.box, veq, isEmpty] at h
  · simp [Code.box, veq, veqList] at h
    omega

/-- A rational's box equals a tagged box only under the code of rationals,
    1 (an integral one is its int, which no tagged box is). -/
theorem box_rational_tagged (V : Variances) (Ξ : HeapTy) (a : Value) (ha : hasTy V Ξ a Code.rational.vty = true)
    (k : Nat) (d : Code) (b : Value)
    (h : veq (Code.rational.box a) ((Code.tagged k d).box b) = true) : k = 1 := by
  cases a <;> simp [Code.vty, hasTy] at ha
  rename_i xs
  rcases xs with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, xs⟩⟩⟩ <;> simp [allTys] at ha
  have hint : ∀ v : Value, hasTy V Ξ v .int = true → ∃ n, v = .int n := by
    intro v hv; cases v <;> simp_all [hasTy]
  obtain ⟨n, rfl⟩ := hint x1 ha.1
  obtain ⟨e, rfl⟩ := hint x2 ha.2
  by_cases he : e = 1
  · simp [Code.box, he, veq, isEmpty] at h
  · simp [Code.box, he, veq, veqList] at h
    omega

/-! ### What Verse identifies stays one value -/

/-- The empty value of a code with no tag boxes to an empty value: `false`,
    `()`, `array{}`, `""` and the empty option, boxed, are all equal
    (`veq_of_isEmpty`). -/
theorem box_empty_plain (c : Code) (hc : c.plain = true) (v : Value) (hv : v.isEmpty = true) :
    (c.box v).isEmpty = true := by
  cases c with
  | id _ => exact hv
  | tuple cs =>
    match v, hv with
    | .tup [], _ => cases cs <;> simp [Code.box, Code.boxL, isEmpty]
    | .logic false, _ | .none, _ => simp [Code.box, isEmpty]
    | .arr a, hv => simpa [Code.box] using hv
  | array c =>
    match v, hv with
    | .tup [], _ | .logic false, _ | .none, _ => simp [Code.box, isEmpty]
    | .arr a, hv => simpa [Code.box, isEmpty] using hv
  | option c =>
    match v, hv with
    | .tup [], _ | .logic false, _ | .none, _ => simp [Code.box, isEmpty]
    | .arr a, hv => simpa [Code.box] using hv
  | _ => simp [Code.plain] at hc

/-- The empty map boxes to the empty value. -/
theorem box_empty_map (ck cv : Code) : ((Code.map ck cv).box (.arr #[])).isEmpty = true := by
  simp [Code.box, isEmpty]

/-- A tuple boxes as the array of its elements (`('a', 'b')` as `"ab"`). -/
theorem box_tuple_array (c : Code) : ∀ (vs : List Value),
    (Code.tuple (List.replicate vs.length c)).box (.tup vs) = (Code.array c).box (.arr vs.toArray)
  | vs => by
    simp only [Code.box]
    congr 1
    have : ∀ (ws : List Value), Code.boxL (List.replicate ws.length c) ws = ws.map (Code.box c) := by
      intro ws; induction ws with
      | nil => rfl
      | cons w ws ih => simp [List.replicate_succ, Code.boxL, ih]
    rw [this]

/-- An integral rational boxes as its int (`4/2` as `2`). -/
theorem box_rational_int (n : Int) :
    Code.rational.box (.tup [.int n, .int 1]) = (Code.id .int).box (.int n) := by
  simp [Code.box]

end OpenVerse
