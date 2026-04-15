

/-
Heap-only rational IDF formalization inspired by Viper Roots.

Design choices:
- heap-only (no store / no trace)
- permissions are non-negative rationals instead of non-negative reals
- function model for masks / heaps
- noncomputable semantic composition is accepted

This version avoids Mathlib. It uses Lean + Std only.

NOTE:
This is a proof-oriented draft. A few proofs are intentionally left as
`sorry` where I cannot honestly certify elaboration without compiling.
The definitions and theorem statements are the main deliverable here.
-/

open Classical

set_option autoImplicit false

-- ============================================================================
-- § 1. preal: non-negative rationals
-- ============================================================================

structure preal where
  val : Rat
  nonneg : 0 ≤ val
  deriving Repr, DecidableEq

namespace preal

@[ext] theorem ext {a b : preal} (h : a.val = b.val) : a = b := by
  cases a
  cases b
  cases h
  rfl

instance : Zero preal := ⟨⟨0, by decide⟩⟩
instance : One preal := ⟨⟨1, by decide⟩⟩
instance : Inhabited preal := ⟨0⟩

instance : Add preal where
  add a b := ⟨a.val + b.val, by unfold preal.val; grind [a.nonneg, b.nonneg]⟩

instance : LE preal where
  le a b := a.val ≤ b.val

instance : LT preal where
  lt a b := a.val < b.val

@[simp] theorem zero_val : (0 : preal).val = 0 := rfl
@[simp] theorem one_val : (1 : preal).val = 1 := rfl
@[simp] theorem add_val (a b : preal) : (a + b).val = a.val + b.val := rfl

@[simp, grind =] theorem preal.add_val (p₁ p₂ : preal) : (p₁ + p₂).val = p₁.val + p₂.val := rfl

@[simp, grind =] theorem preal.one_val : (1 : preal).val = 1 := rfl

@[grind =] theorem preal.mk_eq_mk (v₁ v₂ : Rat) (h₁ h₂) :
    ((⟨v₁, h₁⟩ : preal) = ⟨v₂, h₂⟩) = (v₁ = v₂) := by
  simp [preal.ext_iff]

@[grind =] theorem preal.mk_add_mk_eq_mk (v₁ v₂ v₃ : Rat) (h₁ h₂ h₃) :
    ((⟨v₁, h₁⟩ : preal) + ⟨v₂, h₂⟩ = ⟨v₃, h₃⟩) = (v₁ + v₂ = v₃) := by
  simp [preal.ext_iff]

@[grind =] theorem preal.mk_le_mk (v₁ v₂ : Rat) (h₁ h₂) :
    ((⟨v₁, h₁⟩ : preal) ≤ ⟨v₂, h₂⟩) = (v₁ ≤ v₂) := rfl

@[simp] theorem preal.mk_add_mk_eq_mk' (v₁ v₂ : Rat) (h₁ h₂) :
    ((⟨v₁ + v₂, by grind⟩) = (⟨v₁, h₁⟩ : preal) + ⟨v₂, h₂⟩ ) := by rfl



def ppos (p : preal) : Prop := 0 < p.val

instance (p : preal) : Decidable p.ppos := inferInstanceAs (Decidable (0 < p.val))

def plus (a b : preal) : Option preal := some (a + b)

def core (_ : preal) : preal := 0

def stable (_ : preal) : Prop := True

def stabilize (x : preal) : preal := x

end preal

-- ============================================================================
-- § 2. Values and heap locations
-- ============================================================================

abbrev Address := Nat
abbrev FieldName := String

structure HeapLoc where
  addr : Address
  field : FieldName
  deriving Repr, DecidableEq, BEq

inductive Ref where
  | address : Address → Ref
  | null : Ref
  deriving Repr, DecidableEq, BEq

inductive Val where
  | vInt : Int → Val
  | vBool : Bool → Val
  | vRef : Ref → Val
  | vPerm : Rat → Val
  deriving Repr, DecidableEq, BEq

namespace Val

def plus (a b : Val) : Option Val :=
  if a = b then some a else none

@[simp] theorem plus_self (v : Val) : plus v v = some v := by
  simp [plus]

def core (v : Val) : Val := v

def stable (_ : Val) : Prop := True

def stabilize (v : Val) : Val := v

end Val

-- ============================================================================
-- § 3. Virtual states
-- ============================================================================

abbrev Mask := HeapLoc → preal
abbrev PartialHeap := HeapLoc → Option Val

def wfMaskSimple (π : Mask) : Prop :=
  ∀ hl, π hl ≤ 1

def wfPreVirtualState (π : Mask) (h : PartialHeap) : Prop :=
  (∀ hl, (π hl).ppos → (h hl).isSome) ∧ wfMaskSimple π

structure VirtualState where
  mask : Mask
  heap : PartialHeap
  wf : wfPreVirtualState mask heap

namespace VirtualState

/-- Empty state. -/
def empty : VirtualState where
  mask := fun _ => 0
  heap := fun _ => none
  wf := by
    constructor
    · intro hl hp
      simp [preal.ppos] at hp
    · intro hl
      show (0 : preal) ≤ 1
      change (0 : Rat) ≤ 1
      decide

instance : Inhabited VirtualState := ⟨empty⟩

@[ext] theorem ext {a b : VirtualState}
    (hm : ∀ hl, a.mask hl = b.mask hl)
    (hh : ∀ hl, a.heap hl = b.heap hl) : a = b := by
  cases a with
  | mk am ah awf =>
    cases b with
    | mk bm bh bwf =>
      simp at hm hh
      have hm' : am = bm := funext hm
      have hh' : ah = bh := funext hh
      subst hm'
      subst hh'
      have : awf = bwf := by
        grind
      cases this
      rfl

/-- Read field. -/
def readField (φ : VirtualState) (hl : HeapLoc) : Option Val := φ.heap hl

/-- Permission lookup. -/
def getPerm (φ : VirtualState) (hl : HeapLoc) : preal := φ.mask hl

/-- Positive permission at a location. -/
def hasPerm (φ : VirtualState) (hl : HeapLoc) : Prop := (φ.mask hl).ppos

/-- Heap compatibility: agreement on shared domain. -/
def heapCompatible (h₁ h₂ : PartialHeap) : Prop :=
  ∀ hl v₁ v₂, h₁ hl = some v₁ → h₂ hl = some v₂ → v₁ = v₂

/-- Merge compatible heaps. -/
def heapMerge (h₁ h₂ : PartialHeap) : PartialHeap := fun hl =>
  match h₁ hl, h₂ hl with
  | some v, _ => some v
  | none, some v => some v
  | none, none => none

/-- Disjointness / composability for virtual states. -/
def Disjoint (a b : VirtualState) : Prop :=
  heapCompatible a.heap b.heap ∧
  wfMaskSimple (fun hl => a.mask hl + b.mask hl)

/-- Noncomputable semantic composition of virtual states. -/
noncomputable def plus (a b : VirtualState) : Option VirtualState :=
  if h : Disjoint a b then
    some {
      mask := fun hl => a.mask hl + b.mask hl
      heap := heapMerge a.heap b.heap
      wf := by
        constructor
        · intro hl hp
          have ha : 0 ≤ (a.mask hl).val := (a.mask hl).nonneg
          by_cases hap : (a.mask hl).ppos
          · have hsome := a.wf.1 hl hap
            cases h1 : a.heap hl with
            | none => grind
            | some v =>
                simp [heapMerge, h1]
          · have hap0 : (a.mask hl).val = 0 := by
              have hnotpos : ¬ (0 < (a.mask hl).val) := by
                simpa [preal.ppos] using hap
              grind
            have hp' : 0 < (a.mask hl).val + (b.mask hl).val := by
              simpa [preal.ppos, preal.add_val] using hp
            have hbp : (b.mask hl).ppos := by
              unfold preal.ppos
              rw [hap0] at hp'
              grind
            have hsome := b.wf.1 hl hbp
            cases h2 : b.heap hl with
            | none => grind
            | some v =>
                cases h1 : a.heap hl <;> simp [heapMerge, h1, h2]
        · exact h.2
    }
  else none

open preal in
theorem Disjoint.symm {a b : VirtualState} (h : Disjoint a b) : Disjoint b a := by
  constructor
  · intro hl v₁ v₂ hb ha
    exact (h.1 hl v₂ v₁ ha hb).symm
  · intro hl
    have hle := h.2 hl
    simp_all
    rw[←preal.mk_add_mk_eq_mk']
    rw[←preal.mk_add_mk_eq_mk'] at hle
    grind

open preal in
theorem plus_empty_left (a : VirtualState) : plus empty a = some a := by
  unfold plus
  have hD : Disjoint empty a := by
    constructor
    · intro hl v₁ v₂ h1 _
      simp [empty] at h1
    · intro hl
      simp_all
      simp[empty]
      rw[←preal.mk_add_mk_eq_mk']
      simp
      have :=  a.wf.2 hl
      have hlp (b) : (0:Rat) + b = b := by grind
      simp [hlp]
      apply this
  simp [hD]
  apply VirtualState.ext
  have hlp (a:  VirtualState) b : empty.mask b + a.mask b = a.mask b:=
  by
    simp[empty]
    rw[←preal.mk_add_mk_eq_mk']
    have hlp (b) : (0:Rat) + b = b := by grind
    simp [hlp]
  · grind
  · intro hl
    simp [empty, heapMerge]
    cases h : a.heap hl <;> simp [h]

/-- Stabilize by erasing heap values at zero-permission locations. -/
def stabilize (φ : VirtualState) : VirtualState where
  mask := φ.mask
  heap := fun hl => if (φ.mask hl).ppos then φ.heap hl else none
  wf := by
    constructor
    · intro hl hp
      simp [hp]
      exact φ.wf.1 hl hp
    · exact φ.wf.2

/-- Core preserves values and zeros permissions. -/
def core (φ : VirtualState) : VirtualState where
  mask := fun _ => 0
  heap := φ.heap
  wf := by
    constructor
    · intro hl hp
      simp [preal.ppos] at hp
    · intro hl
      show (0 : preal) ≤ 1
      change (0 : Rat) ≤ 1
      decide

@[simp] theorem stabilize_mask (φ : VirtualState) (hl : HeapLoc) :
    (stabilize φ).mask hl = φ.mask hl := rfl

@[simp] theorem stabilize_heap (φ : VirtualState) (hl : HeapLoc) :
    (stabilize φ).heap hl = if (φ.mask hl).ppos then φ.heap hl else none := rfl

/-- Repo-style stability: every present heap value has positive permission. -/
def Stable (φ : VirtualState) : Prop :=
  ∀ hl v, φ.heap hl = some v → (φ.mask hl).ppos

theorem stabilize_stable (φ : VirtualState) : (stabilize φ).Stable := by
  intro hl v hheap
  simp [Stable, stabilize] at hheap ⊢
  grind

/-- Stable states are fixed by stabilize. -/
theorem stable_eq_stabilize {φ : VirtualState} (hs : φ.Stable) :
    stabilize φ = φ := by
  apply VirtualState.ext
  · intro hl
    rfl
  · intro hl
    simp [stabilize]
    by_cases hp : (φ.mask hl).ppos
    · simp [hp]
    · simp [hp]
      cases hheap : φ.heap hl with
      | none => rfl
      | some v =>
          exfalso
          exact hp (hs hl v hheap)

/-- Conversely, if stabilize is identity, the state was stable. -/
theorem stable_of_eq_stabilize {φ : VirtualState}
    (h : stabilize φ = φ) : φ.Stable := by
  intro hl v hheap
  have h' := congrArg (fun s => s.heap hl) h
  simp [stabilize, hheap] at h'
  by_cases hp : (φ.mask hl).ppos
  · exact hp
  · simp [hp, hheap] at h'

end VirtualState

-- ============================================================================
-- § 4. Assertions
-- ============================================================================

abbrev Assertion := VirtualState → Prop

namespace Assertion

/-- Entailment between semantic assertions. -/
def entails (P Q : Assertion) : Prop :=
  ∀ φ, P φ → Q φ

infix:55 " ⊢ " => entails

/-- Semantic separating conjunction. -/
def sep (P Q : Assertion) : Assertion :=
  fun φ => ∃ φ₁ φ₂,
    VirtualState.plus φ₁ φ₂ = some φ ∧
    P φ₁ ∧ Q φ₂

infixr:70 " ∗ " => sep

/-- Empty assertion. -/
def emp : Assertion :=
  fun φ => φ = VirtualState.empty

/-- Self-framing = stabilization invariance. -/
def SelfFraming (P : Assertion) : Prop :=
  ∀ φ, P φ ↔ P (VirtualState.stabilize φ)

/-- Accessibility assertion: enough permission at a location. -/
def acc (hl : HeapLoc) (p : preal) : Assertion :=
  fun φ => p.ppos ∧ p ≤ φ.mask hl

/-- Heap-dependent value assertion. -/
def fieldEq (hl : HeapLoc) (v : Val) : Assertion :=
  fun φ => φ.heap hl = some v

/-- Direct bundled points-to assertion, best for first proofs. -/
def pointsToDirect (hl : HeapLoc) (p : preal) (v : Val) : Assertion :=
  fun φ => p.ppos ∧ p ≤ φ.mask hl ∧ φ.heap hl = some v

/-- Separation-style bundled assertion. -/
def pointsToFrac (hl : HeapLoc) (p : preal) (v : Val) : Assertion :=
  acc hl p ∗ fieldEq hl v

/-- Full-permission points-to. -/
def pointsTo (hl : HeapLoc) (v : Val) : Assertion :=
  pointsToDirect hl 1 v

theorem mem_sep_intro {P Q : Assertion} {φ φ₁ φ₂ : VirtualState}
    (hplus : VirtualState.plus φ₁ φ₂ = some φ)
    (hP : P φ₁)
    (hQ : Q φ₂) :
    (P ∗ Q) φ := by
  exact ⟨φ₁, φ₂, hplus, hP, hQ⟩

theorem selfFraming_acc (hl : HeapLoc) (p : preal) :
    SelfFraming (acc hl p) := by
  intro φ
  simp [acc, VirtualState.stabilize]

theorem fieldEq_of_perm {φ : VirtualState} {hl : HeapLoc} {v : Val}
    (hperm : (φ.mask hl).ppos)
    (hEq : fieldEq hl v φ) :
    fieldEq hl v (VirtualState.stabilize φ) := by
  simp [fieldEq, VirtualState.stabilize, hperm]
  unfold fieldEq at hEq
  apply hEq

/-- Heap-dependent equality is not generally self-framing, but it is preserved
    by stabilization when permission is present. -/
theorem selfFraming_pointsToDirect (hl : HeapLoc) (p : preal) (v : Val) :
    SelfFraming (pointsToDirect hl p v) := by
  intro φ
  constructor
  · intro h
    rcases h with ⟨hp, hle, hheap⟩
    have hppos : (φ.mask hl).ppos := by
      unfold preal.ppos at hp
      unfold preal.ppos
      unfold LE.le at hle
      unfold preal.instLE at hle
      simp at hle
      grind
    refine ⟨hp, ?_, ?_⟩
    · simpa [VirtualState.stabilize] using hle
    · simpa [VirtualState.stabilize, hppos] using hheap
  · intro h
    rcases h with ⟨hp, hle, hheap⟩
    refine ⟨hp, ?_, ?_⟩
    · simpa [VirtualState.stabilize] using hle
    · have hppos : (φ.mask hl).ppos := by
        unfold preal.ppos at hp
        unfold preal.ppos
        unfold LE.le at hle
        unfold preal.instLE at hle
        simp at hle
        grind
      simpa [VirtualState.stabilize, hppos] using hheap

theorem pointsToDirect_entails_acc (hl : HeapLoc) (p : preal) (v : Val) :
    pointsToDirect hl p v ⊢ acc hl p := by
  intro φ h
  exact ⟨h.1, h.2.1⟩

theorem pointsToDirect_entails_fieldEq (hl : HeapLoc) (p : preal) (v : Val) :
    pointsToDirect hl p v ⊢ fieldEq hl v := by
  intro φ h
  exact h.2.2

end Assertion

-- ============================================================================
-- § 5. Example: acc(p.f) && p.f == 5
-- ============================================================================

namespace Examples

open Assertion

/-- Example heap location p.f. -/
def pf (pAddr : Address) : HeapLoc := ⟨pAddr, "f"⟩

/-- Direct bundled version of acc(p.f) && p.f == 5. -/
def ex1 (pAddr : Address) : Assertion :=
  pointsToDirect (pf pAddr) 1 (Val.vInt 5)

/-- Separation-style spelling of the same intended assertion. -/
def ex1_sep (pAddr : Address) : Assertion :=
  acc (pf pAddr) 1 ∗ fieldEq (pf pAddr) (Val.vInt 5)

theorem ex1_selfFraming (pAddr : Address) :
    SelfFraming (ex1 pAddr) := by
  simpa [ex1] using selfFraming_pointsToDirect (pf pAddr) 1 (Val.vInt 5)

end Examples
