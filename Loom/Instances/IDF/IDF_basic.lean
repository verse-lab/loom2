

open Classical

set_option autoImplicit false

-- ============================================================================
-- § 1. preal: non-negative rationals  (unchanged from user's version)
-- ============================================================================

structure preal where
  val : Rat
  nonneg : 0 ≤ val
  deriving Repr, DecidableEq

namespace preal

@[ext] theorem ext {a b : preal} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

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
    ((⟨v₁, h₁⟩ : preal) = ⟨v₂, h₂⟩) = (v₁ = v₂) := by simp [preal.ext_iff]

@[grind =] theorem preal.mk_add_mk_eq_mk (v₁ v₂ v₃ : Rat) (h₁ h₂ h₃) :
    ((⟨v₁, h₁⟩ : preal) + ⟨v₂, h₂⟩ = ⟨v₃, h₃⟩) = (v₁ + v₂ = v₃) := by simp [preal.ext_iff]

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
-- § 2. Values and heap locations  (unchanged)
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
def plus (a b : Val) : Option Val := if a = b then some a else none
@[simp] theorem plus_self (v : Val) : plus v v = some v := by simp [plus]
def core (v : Val) : Val := v
def stable (_ : Val) : Prop := True
def stabilize (v : Val) : Val := v
end Val

-- ============================================================================
-- § 3. Virtual states  (unchanged)
-- ============================================================================

abbrev Mask := HeapLoc → preal
abbrev PartialHeap := HeapLoc → Option Val

def wfMaskSimple (π : Mask) : Prop := ∀ hl, π hl ≤ 1

def wfPreVirtualState (π : Mask) (h : PartialHeap) : Prop :=
  (∀ hl, (π hl).ppos → (h hl).isSome) ∧ wfMaskSimple π

structure VirtualState where
  mask : Mask
  heap : PartialHeap
  wf : wfPreVirtualState mask heap

namespace VirtualState

def empty : VirtualState where
  mask := fun _ => 0
  heap := fun _ => none
  wf := by
    constructor
    · intro hl hp; simp [preal.ppos] at hp
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
      subst hm'; subst hh'
      have : awf = bwf := by grind
      cases this; rfl

def readField (φ : VirtualState) (hl : HeapLoc) : Option Val := φ.heap hl
def getPerm (φ : VirtualState) (hl : HeapLoc) : preal := φ.mask hl
def hasPerm (φ : VirtualState) (hl : HeapLoc) : Prop := (φ.mask hl).ppos

def heapCompatible (h₁ h₂ : PartialHeap) : Prop :=
  ∀ hl v₁ v₂, h₁ hl = some v₁ → h₂ hl = some v₂ → v₁ = v₂

def heapMerge (h₁ h₂ : PartialHeap) : PartialHeap := fun hl =>
  match h₁ hl, h₂ hl with
  | some v, _ => some v
  | none, some v => some v
  | none, none => none

def Disjoint (a b : VirtualState) : Prop :=
  heapCompatible a.heap b.heap ∧
  wfMaskSimple (fun hl => a.mask hl + b.mask hl)

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
            | some v => simp [heapMerge, h1]
          · have hap0 : (a.mask hl).val = 0 := by
              have hnotpos : ¬ (0 < (a.mask hl).val) := by simpa [preal.ppos] using hap
              grind
            have hp' : 0 < (a.mask hl).val + (b.mask hl).val := by
              simpa [preal.ppos, preal.add_val] using hp
            have hbp : (b.mask hl).ppos := by
              unfold preal.ppos; rw [hap0] at hp'; grind
            have hsome := b.wf.1 hl hbp
            cases h2 : b.heap hl with
            | none => grind
            | some v => cases h1 : a.heap hl <;> simp [heapMerge, h1, h2]
        · exact h.2
    }
  else none

open preal in
theorem Disjoint.symm {a b : VirtualState} (h : Disjoint a b) : Disjoint b a := by
  constructor
  · intro hl v₁ v₂ hb ha; exact (h.1 hl v₂ v₁ ha hb).symm
  · intro hl
    have hle := h.2 hl
    simp_all
    rw[←preal.mk_add_mk_eq_mk']
    rw[←preal.mk_add_mk_eq_mk'] at hle
    grind

theorem disjoint_of_plus {a b x : VirtualState}
    (h : plus a b = some x) : Disjoint a b := by
  unfold plus at h
  split at h
  rename_i hD
  · exact hD
  · simp at h

theorem plus_mask {a b x : VirtualState}
    (h : plus a b = some x) :
    ∀ hl, x.mask hl = a.mask hl + b.mask hl := by
  intro hl
  unfold plus at h
  split at h
  rename_i hD
  · simp at h
    subst h
    rfl
  · simp at h

theorem plus_heap {a b x : VirtualState}
    (h : plus a b = some x) :
    ∀ hl, x.heap hl = heapMerge a.heap b.heap hl := by
  intro hl
  unfold plus at h
  split at h
  rename_i hD
  · simp at h
    subst h
    rfl
  · simp at h

theorem heapMerge_eq_left_of_compatible
    {h₁ h₂ : PartialHeap} {hl : HeapLoc} {v : Val}
    (hcomp : heapCompatible h₁ h₂)
    (h1 : h₁ hl = some v) :
    heapMerge h₁ h₂ hl = some v := by
  unfold heapMerge
  cases h2 : h₂ hl with
  | none =>
      simp [h1]
  | some v2 =>
      have hv : v = v2 := hcomp hl v v2 h1 h2
      simp [h1, hv]

theorem heapMerge_eq_right_of_compatible
    {h₁ h₂ : PartialHeap} {hl : HeapLoc} {v : Val}
    (hcomp : heapCompatible h₁ h₂)
    (h2 : h₂ hl = some v) :
    heapMerge h₁ h₂ hl = some v := by
  unfold heapMerge
  cases h1 : h₁ hl with
  | none =>
      simp [h2]
  | some v1 =>
      have hv : v1 = v := hcomp hl v1 v h1 h2
      simp [hv]

theorem heapMerge_assoc
    {h₁ h₂ h₃ : PartialHeap}
    (h12 : heapCompatible h₁ h₂)
    (h23 : heapCompatible h₂ h₃)
    (h13 : heapCompatible h₁ h₃) :
    ∀ hl, heapMerge (heapMerge h₁ h₂) h₃ hl = heapMerge h₁ (heapMerge h₂ h₃) hl := by
  intro hl
  unfold heapMerge
  cases h1 : h₁ hl with
  | none =>
      cases h2 : h₂ hl with
      | none =>
          cases h3 : h₃ hl <;> simp
      | some v2 =>
          cases h3 : h₃ hl with
          | none =>
              simp
          | some v3 =>
              have hv : v2 = v3 := h23 hl v2 v3 h2 h3
              simp
  | some v1 =>
      cases h2 : h₂ hl with
      | none =>
          cases h3 : h₃ hl with
          | none =>
              simp
          | some v3 =>
              have hv : v1 = v3 := h13 hl v1 v3 h1 h3
              simp
      | some v2 =>
          have hv12 : v1 = v2 := h12 hl v1 v2 h1 h2
          cases h3 : h₃ hl with
          | none =>
              simp
          | some v3 =>
              have hv13 : v1 = v3 := h13 hl v1 v3 h1 h3
              have hv23 : v2 = v3 := h23 hl v2 v3 h2 h3
              simp [hv12, hv23]

open preal in
theorem plus_assoc_exists
    {a b c ab x : VirtualState}
    (hab : plus a b = some ab)
    (hxc : plus ab c = some x) :
    ∃ bc, plus b c = some bc ∧ plus a bc = some x := by
  let bc : VirtualState :=
    { mask := fun hl => b.mask hl + c.mask hl
      heap := heapMerge b.heap c.heap
      wf := by
        constructor
        · intro hl hp
          have hb_nonneg : 0 ≤ (b.mask hl).val := (b.mask hl).nonneg
          by_cases hbp : (b.mask hl).ppos
          · have hs : (b.heap hl).isSome := b.wf.1 hl hbp
            cases hb : b.heap hl with
            | none =>
                simp [hb] at hs
            | some vb =>
                simp [heapMerge, hb]
          · have hbp0 : (b.mask hl).val = 0 := by
              have hnot : ¬ 0 < (b.mask hl).val := by simpa [preal.ppos] using hbp
              grind
            have hp' : 0 < (b.mask hl).val + (c.mask hl).val := by
              simpa [preal.ppos, preal.add_val] using hp
            have hcp : (c.mask hl).ppos := by
              unfold preal.ppos
              rw [hbp0] at hp'
              grind
            have hs : (c.heap hl).isSome := c.wf.1 hl hcp
            cases hc : c.heap hl with
            | none =>
                simp [hc] at hs
            | some vc =>
                cases hb : b.heap hl <;> simp [heapMerge, hb, hc]
        · intro hl
          have hDab : Disjoint a b := disjoint_of_plus hab
          have hDxc : Disjoint ab c := disjoint_of_plus hxc
          have habMask := plus_mask hab hl
          have habcBound : ab.mask hl + c.mask hl ≤ (1 : preal) := hDxc.2 hl
          show b.mask hl + c.mask hl ≤ (1 : preal)
          show (b.mask hl + c.mask hl).val ≤ 1
          simp [habMask] at habcBound
          have ha_nonneg : 0 ≤ (a.mask hl).val := (a.mask hl).nonneg
          have hb_nonneg : 0 ≤ (b.mask hl).val := (b.mask hl).nonneg
          have hc_nonneg : 0 ≤ (c.mask hl).val := (c.mask hl).nonneg
          simp [preal.add_val] at habcBound ⊢
          unfold HAdd.hAdd at habcBound
          unfold instHAdd at habcBound
          simp at habcBound
          unfold Add.add at habcBound
          unfold instAdd at habcBound
          simp at habcBound
          unfold LE.le at habcBound
          unfold instLE at habcBound
          grind  }

  have hDab : Disjoint a b := disjoint_of_plus hab
  have hDxc : Disjoint ab c := disjoint_of_plus hxc

  have hDbc : Disjoint b c := by
    constructor
    · intro hl vb vc hb hc
      have habHeap : ab.heap hl = some vb := by
        rw [plus_heap hab hl]
        exact heapMerge_eq_right_of_compatible hDab.1 hb
      exact hDxc.1 hl vb vc habHeap hc
    · intro hl
      have habMask := plus_mask hab hl
      have habcBound : ab.mask hl + c.mask hl ≤ (1 : preal) := hDxc.2 hl
      show b.mask hl + c.mask hl ≤ (1 : preal)
      show (b.mask hl + c.mask hl).val ≤ 1
      rw [habMask] at habcBound
      have ha_nonneg : 0 ≤ (a.mask hl).val := (a.mask hl).nonneg
      simp [preal.add_val] at habcBound ⊢
      unfold HAdd.hAdd at habcBound
      unfold instHAdd at habcBound
      simp at habcBound
      unfold Add.add at habcBound
      unfold instAdd at habcBound
      simp at habcBound
      unfold LE.le at habcBound
      unfold instLE at habcBound
      grind

  have hbc : plus b c = some bc := by
    unfold plus
    simp [hDbc]
    apply VirtualState.ext
    · intro hl
      rfl
    · intro hl
      rfl

  have hDabc : Disjoint a bc := by
    constructor
    · intro hl va vbc ha hvbc
      change heapMerge b.heap c.heap hl = some vbc at hvbc
      cases hb : b.heap hl with
      | none =>
          cases hc : c.heap hl with
          | none =>
              unfold heapMerge at hvbc
              simp [hb, hc] at hvbc
          | some vc =>
              have hab_va : ab.heap hl = some va := by
                rw [plus_heap hab hl]
                exact heapMerge_eq_left_of_compatible hDab.1 ha
              have hvc_eq_vbc : vc = vbc := by
                have h_m : heapMerge b.heap c.heap hl = some vbc := hvbc
                unfold heapMerge at h_m
                simp [hb, hc] at h_m
                exact h_m
              subst hvc_eq_vbc
              exact hDxc.1 hl va _ hab_va hc
      | some vb =>
          have hva_eq_vb := hDab.1 hl va vb ha hb
          have hvb_eq_vbc : vb = vbc := by
            have h_m : heapMerge b.heap c.heap hl = some vbc := hvbc
            unfold heapMerge at h_m
            simp [hb] at h_m
            exact h_m
          rw [hva_eq_vb, hvb_eq_vbc]
    · intro hl
      have hbcMask : bc.mask hl = b.mask hl + c.mask hl := rfl
      have habMask := plus_mask hab hl
      have hxcMask := plus_mask hxc hl
      have hxabound : a.mask hl + bc.mask hl ≤ (1 : preal) := by
        rw [hbcMask]
        have hbound := hDxc.2 hl

        show (a.mask hl + (b.mask hl + c.mask hl)).val ≤ (1 : preal).val
        have h1 : (a.mask hl + (b.mask hl + c.mask hl)).val = (a.mask hl + b.mask hl + c.mask hl).val := by
          simp only [preal.add_val]
          grind
        rw [h1]
        change ab.mask hl + c.mask hl ≤ 1 at hbound
        rw [habMask] at hbound
        exact hbound
      exact hxabound

  have hax : plus a bc = some x := by
    unfold plus
    simp [hDabc]
    apply VirtualState.ext
    · intro hl
      change a.mask hl + (b.mask hl + c.mask hl) = x.mask hl
      rw [plus_mask hxc hl, plus_mask hab hl]
      apply preal.ext
      simp only [preal.add_val]
      grind

    · intro hl
      show heapMerge a.heap bc.heap hl = x.heap hl
      rw [plus_heap hxc hl]
      have hab_eq : ab.heap = heapMerge a.heap b.heap := funext (plus_heap hab)
      have hbc_eq : bc.heap = heapMerge b.heap c.heap := funext (plus_heap hbc)
      rw [hab_eq, hbc_eq]

      have hac_comp : heapCompatible a.heap c.heap := by
        intro hl' va' vc' ha' hc'
        have hab_va : ab.heap hl' = some va' := by
          rw [plus_heap hab hl']
          exact heapMerge_eq_left_of_compatible hDab.1 ha'
        exact hDxc.1 hl' va' vc' hab_va hc'
      exact (heapMerge_assoc hDab.1 hDbc.1 hac_comp hl).symm
  exact ⟨bc, hbc, hax⟩



open preal in
theorem plus_empty_left (a : VirtualState) : plus empty a = some a := by
  unfold plus
  have hD : Disjoint empty a := by
    constructor
    · intro hl v₁ v₂ h1 _; simp [empty] at h1
    · intro hl
      simp_all; simp[empty]
      rw[←preal.mk_add_mk_eq_mk']; simp
      have := a.wf.2 hl
      have hlp (b) : (0:Rat) + b = b := by grind
      simp [hlp]; apply this
  simp [hD]
  apply VirtualState.ext
  have hlp (a : VirtualState) b : empty.mask b + a.mask b = a.mask b := by
    simp[empty]
    rw[←preal.mk_add_mk_eq_mk']
    have hlp (b) : (0:Rat) + b = b := by grind
    simp [hlp]
  · grind
  · intro hl
    simp [empty, heapMerge]
    cases h : a.heap hl <;> simp

def stabilize (φ : VirtualState) : VirtualState where
  mask := φ.mask
  heap := fun hl => if (φ.mask hl).ppos then φ.heap hl else none
  wf := by
    constructor
    · intro hl hp; simp [hp]; exact φ.wf.1 hl hp
    · exact φ.wf.2

def core (φ : VirtualState) : VirtualState where
  mask := fun _ => 0
  heap := φ.heap
  wf := by
    constructor
    · intro hl hp; simp [preal.ppos] at hp
    · intro hl
      show (0 : preal) ≤ 1
      change (0 : Rat) ≤ 1
      decide

@[simp] theorem stabilize_mask (φ : VirtualState) (hl : HeapLoc) :
    (stabilize φ).mask hl = φ.mask hl := rfl

@[simp] theorem stabilize_heap (φ : VirtualState) (hl : HeapLoc) :
    (stabilize φ).heap hl = if (φ.mask hl).ppos then φ.heap hl else none := rfl

@[simp] theorem core_mask (φ : VirtualState) (hl : HeapLoc) :
    (core φ).mask hl = 0 := rfl

@[simp] theorem core_heap (φ : VirtualState) (hl : HeapLoc) :
    (core φ).heap hl = φ.heap hl := rfl

/-- stabilize φ = φ -/
def Stable (φ : VirtualState) : Prop :=
  ∀ hl v, φ.heap hl = some v → (φ.mask hl).ppos

theorem stabilize_stable (φ : VirtualState) : (stabilize φ).Stable := by
  intro hl v hheap
  simp [stabilize] at hheap ⊢
  grind

theorem stable_eq_stabilize {φ : VirtualState} (hs : φ.Stable) :
    stabilize φ = φ := by
  apply VirtualState.ext
  · intro hl; rfl
  · intro hl
    simp [stabilize]
    by_cases hp : (φ.mask hl).ppos
    · simp [hp]
    · simp [hp]
      cases hheap : φ.heap hl with
      | none => rfl
      | some v => exfalso; exact hp (hs hl v hheap)

theorem stable_of_eq_stabilize {φ : VirtualState}
    (h : stabilize φ = φ) : φ.Stable := by
  intro hl v hheap
  have h' := congrArg (fun s => s.heap hl) h
  simp [stabilize, hheap] at h'
  by_cases hp : (φ.mask hl).ppos
  · exact hp
  · simp [hp] at h'

-- ============================================================================
-- § 4. Abstract sep_algebra laws, concretely proved
-- ============================================================================
-- These correspond to axioms/lemmas in Isabelle's SepAlgebraDef.thy, extended
-- by the concrete Viper instantiation in EquiViper.thy. They are the tools
-- Dardinier uses in SepLogic.thy to reason about emp, ⊗, self_framing.

/-- Empty is the right identity of plus. -/
theorem plus_empty_right (a : VirtualState) : plus a empty = some a := by
  unfold plus
  have hD : Disjoint a empty := by
    refine ⟨?_, ?_⟩
    · intro hl v₁ v₂ _ h2; simp [empty] at h2
    · intro hl
      have := a.wf.2 hl
      show a.mask hl + empty.mask hl ≤ 1
      have : a.mask hl + empty.mask hl = a.mask hl := by
        apply preal.ext
        simp [empty]
        grind
      rw [this]; exact a.wf.2 hl
  simp [hD]
  apply VirtualState.ext
  · intro hl
    show a.mask hl + empty.mask hl = a.mask hl
    apply preal.ext; simp [empty]
    grind
  · intro hl
    simp [empty, heapMerge]
    cases h : a.heap hl <;> simp

/-- **Key fact for the Isabelle-style `emp`**:
    `stabilize (core φ) = VirtualState.empty` for every φ.

    Because `core` zeros the mask, and `stabilize` erases heap values where
    mask is zero — which is everywhere, after core.

    Consequence: the Isabelle `emp = {stabilize |b| | b}` collapses to `{empty}`. -/
theorem stabilize_core_eq_empty (φ : VirtualState) :
    stabilize (core φ) = empty := by
  apply VirtualState.ext
  · intro hl; rfl
  · intro hl
    simp [stabilize, core, empty, preal.ppos]

/-- **`decompose_stabilize_pure`** (Isabelle sep_algebra axiom):
    every state is the combination of its stable part and its core.

    `Some φ = stabilize φ ⊕ core φ`

    This is the law that justifies why combining with `stabilize |b|`
    (which is the unit) gives back the original. -/
theorem decompose_stabilize_pure (φ : VirtualState) :
    plus (stabilize φ) (core φ) = some φ := by
  unfold plus
  have hD : Disjoint (stabilize φ) (core φ) := by
    refine ⟨?_, ?_⟩
    · intro hl v₁ v₂ he₁ he₂
      -- stabilize.heap hl = if ppos then φ.heap hl else none
      -- core.heap hl = φ.heap hl
      simp [stabilize] at he₁
      simp [core] at he₂
      by_cases hp : (φ.mask hl).ppos
      · simp [hp] at he₁
        rw [he₁] at he₂
        exact Option.some.inj he₂
      · simp [hp] at he₁
    · intro hl
      show (stabilize φ).mask hl + (core φ).mask hl ≤ 1
      have h1 : (stabilize φ).mask hl + (core φ).mask hl = φ.mask hl := by
        apply preal.ext
        simp [stabilize, core]
        grind
      rw [h1]; exact φ.wf.2 hl
  simp [hD]
  apply VirtualState.ext
  · intro hl
    show (stabilize φ).mask hl + (core φ).mask hl = φ.mask hl
    apply preal.ext; simp [stabilize, core]
    grind
  · intro hl
    simp [heapMerge, stabilize, core]
    by_cases hp : (φ.mask hl).ppos
    · simp [hp]
      cases φ.heap hl <;> rfl
    · simp [hp]
      -- We need: (merge none (φ.heap hl)) = φ.heap hl
      -- merge none x = x by definition
      cases φ.heap hl <;> rfl




/-- **`stabilize_core_emp`** (Isabelle sep_algebra axiom):
    combining with `stabilize (core c)` is the identity.

    This is what makes `A ⊗ emp = A` work — since `emp` is exactly the
    set of stabilized cores, combining with any element of `emp` returns
    the original state. -/
theorem stabilize_core_emp {a b c : VirtualState}
    (h : plus b (stabilize (core c)) = some a) : a = b := by
  rw [stabilize_core_eq_empty] at h
  rw [plus_empty_right] at h
  exact (Option.some.inj h).symm

/-- Symmetric version of the above (combining with stabilize (core _) on the left). -/
theorem stabilize_core_emp_left {a b c : VirtualState}
    (h : plus (stabilize (core c)) b = some a) : a = b := by
  rw [stabilize_core_eq_empty] at h
  rw [plus_empty_left] at h
  exact (Option.some.inj h).symm

/-- Concrete `stabilize_sum`, matching the abstract sep-algebra law:
    if `a ⊕ b = x`, then `stabilize a ⊕ stabilize b = stabilize x`. -/
theorem stabilize_sum {a b x : VirtualState}
    (h : plus a b = some x) :
    plus (stabilize a) (stabilize b) = some (stabilize x) := by
  unfold plus at h ⊢
  split at h
  rename_i hD
  · simp at h; subst h
    · have hD' : Disjoint (stabilize a) (stabilize b) := by
        constructor
        · intro hl v₁ v₂ ha hb
          simp [stabilize] at ha hb
          by_cases hpa : (a.mask hl).ppos <;> by_cases hpb : (b.mask hl).ppos <;> simp [hpa, hpb] at ha hb
          · exact hD.1 hl v₁ v₂ ha hb
        · intro hl
          simpa [stabilize]
            using hD.2 hl
      simp [hD']
      apply VirtualState.ext
      · intro hl
        rfl
      · intro hl
        simp [stabilize, heapMerge]
        by_cases hpa : (a.mask hl).ppos <;> by_cases hpb : (b.mask hl).ppos <;> simp [hpa, hpb]
        ·
          -- both positive
          cases ha : a.heap hl with
          | none =>
              have : (a.heap hl).isSome := a.wf.1 hl hpa
              simp [ha] at this
          | some va =>
              cases hb : b.heap hl with
              | none =>
                  have : (b.heap hl).isSome := b.wf.1 hl hpb
                  simp [hb] at this
              | some vb =>
                  have hEq : va = vb := hD.1 hl va vb ha hb
                  simp [hEq]
                  unfold preal.ppos at hpa hpb
                  unfold preal.ppos
                  grind
        ·
          cases ha : a.heap hl with
          | none =>
              have : (a.heap hl).isSome := a.wf.1 hl hpa
              simp [ha] at this
          | some va =>
              have hsum_pos : (a.mask hl + b.mask hl).ppos := by
                unfold preal.ppos at hpa ⊢
                have hb_nonneg : 0 ≤ (b.mask hl).val := (b.mask hl).nonneg
                simp [preal.add_val] at *
                grind
              grind
        ·
          -- a not positive, b positive
          have hbSome : (b.heap hl).isSome := b.wf.1 hl hpb
          cases hb : b.heap hl with
          | none =>
              simp [hb] at hbSome
          | some vb =>
              have hsum_pos : (a.mask hl + b.mask hl).ppos := by
                unfold preal.ppos at hpb ⊢
                have ha_nonneg : 0 ≤ (a.mask hl).val := (a.mask hl).nonneg
                simp [preal.add_val] at *
                grind
              simp [hsum_pos]
              cases ha : a.heap hl with
              | none =>
                  simp
              | some va =>
                  have hEq : va = vb := hD.1 hl va vb ha hb
                  simp [hEq]
        ·
          -- neither positive
          intro hsum_pos
          unfold preal.ppos at hpa hpb hsum_pos
          simp [preal.add_val] at hsum_pos
          have ha_nonneg : 0 ≤ (a.mask hl).val := (a.mask hl).nonneg
          have hb_nonneg : 0 ≤ (b.mask hl).val := (b.mask hl).nonneg
          grind
  grind



end VirtualState

-- ============================================================================
-- § 5. Assertions and emp (Isabelle-style)
-- ============================================================================

abbrev Assertion := VirtualState → Prop

namespace Assertion

@[grind] def entails (P Q : Assertion) : Prop := ∀ φ, P φ → Q φ


infix:55 " ⊢ " => entails

def sep (P Q : Assertion) : Assertion :=
  fun φ => ∃ φ₁ φ₂, VirtualState.plus φ₁ φ₂ = some φ ∧ P φ₁ ∧ Q φ₂
infixr:70 " ∗ " => sep

/-- **`emp`, Isabelle-faithful**: the image of stabilize ∘ core.

    In Isabelle: `emp = {a. ∃b. a = stabilize |b|}`.
    In our concrete model, since `stabilize (core b) = empty` for every b,
    this collapses to the singleton `{VirtualState.empty}`. -/
def emp : Assertion := fun φ => ∃ b : VirtualState, φ = VirtualState.stabilize (VirtualState.core b)

/-- Extensional characterization: `emp = {VirtualState.empty}`. -/
theorem emp_iff_empty (φ : VirtualState) : emp φ ↔ φ = VirtualState.empty := by
  constructor
  · rintro ⟨b, hb⟩
    rw [hb]
    exact VirtualState.stabilize_core_eq_empty b
  · intro heq
    exact ⟨VirtualState.empty, by rw [heq]; exact (VirtualState.stabilize_core_eq_empty _).symm⟩

/-- Self-framing, Isabelle-style: `P φ ↔ P (stabilize φ)`. -/
def SelfFraming (P : Assertion) : Prop :=
  ∀ φ, P φ ↔ P (VirtualState.stabilize φ)


/-- Assertion-level stabilization, Isabelle-style:
    `Stabilize A = {ω. stabilize ω ∈ A}`. -/
def Stabilize (A : Assertion) : Assertion :=
  fun φ => A (VirtualState.stabilize φ)

/-- The stabilized empty assertion used in the frontend proofs. -/
def semp : Assertion := Stabilize emp

/-- Isabelle's `Stable A ≡ A ⊆ Stabilize A`. -/
def StableAssert (A : Assertion) : Prop :=
  A ⊢ Stabilize A

/-- `Stabilize A` is always self-framing. This is the direct Lean analogue of
    Isabelle's `Stabilize_self_framing[simp]`. -/
theorem Stabilize_selfFraming (A : Assertion) :
    SelfFraming (Stabilize A) := by
  intro φ
  unfold Stabilize
  constructor <;> intro h
  ·
    -- need A (stabilize (stabilize φ))
    simpa [VirtualState.stable_eq_stabilize (VirtualState.stabilize_stable φ)] using h
  ·
    -- rewrite backwards using idempotence of stabilize
    simpa [VirtualState.stable_eq_stabilize (VirtualState.stabilize_stable φ)] using h

/-- `semp` is self-framing immediately. -/
theorem selfFraming_semp : SelfFraming semp := by
  unfold semp
  exact Stabilize_selfFraming emp

/-- Concrete characterization of `semp`:
    `semp φ` iff `stabilize φ = empty`. -/
theorem semp_iff_stabilize_empty (φ : VirtualState) :
    semp φ ↔ VirtualState.stabilize φ = VirtualState.empty := by
  unfold semp Stabilize
  rw [emp_iff_empty]

/-- `emp` is stable in the Isabelle sense `A ⊆ Stabilize A`. -/
theorem StableAssert_emp : StableAssert emp := by
  intro φ hφ
  unfold Stabilize
  unfold emp
  unfold emp at hφ
  rcases hφ with ⟨b, hb⟩
  simp[hb]
  exists b

/-- `semp` is stable as well. -/
theorem StableAssert_semp : StableAssert semp := by
  intro φ hφ
  unfold semp Stabilize at hφ ⊢
  simpa [VirtualState.stable_eq_stabilize (VirtualState.stabilize_stable φ)] using hφ

/-- Every assertion entails its star with `semp`.
    This corresponds to the way `Stabilize emp` is used in the frontend proofs. -/
theorem entails_star_semp (A : Assertion) : A ⊢ A ∗ semp := by
  intro φ hA
  refine ⟨φ, VirtualState.empty, ?_, hA, ?_⟩
  · exact VirtualState.plus_empty_right φ
  · unfold semp Stabilize
    rw [emp_iff_empty]
    apply VirtualState.ext
    · intro hl
      rfl
    · intro hl
      simp [VirtualState.stabilize, VirtualState.empty, preal.ppos]

/-- If `A` is self-framing, then `A ∗ semp ⊢ A`.

    This is the useful IDF theorem: `semp` is not a raw unit for arbitrary
    assertions, but it is absorbed by self-framing assertions. -/
theorem star_semp_entails_of_selfFraming (A : Assertion)
    (hA : SelfFraming A) :
    A ∗ semp ⊢ A := by
  intro φ hφ
  rcases hφ with ⟨φ₁, φ₂, hplus, hφ₁A, hφ₂semp⟩

  have hφ₁st : A (VirtualState.stabilize φ₁) := (hA φ₁).mp hφ₁A
  have hφ₂empty : VirtualState.stabilize φ₂ = VirtualState.empty :=
    (semp_iff_stabilize_empty φ₂).mp hφ₂semp

  have hsum :
      VirtualState.plus (VirtualState.stabilize φ₁) (VirtualState.stabilize φ₂) =
      some (VirtualState.stabilize φ) := by
    apply VirtualState.stabilize_sum
    apply hplus

  rw [hφ₂empty, VirtualState.plus_empty_right] at hsum
  have hEq : VirtualState.stabilize φ₁ = VirtualState.stabilize φ := by
    exact Option.some.inj hsum

  have hφst : A (VirtualState.stabilize φ) := by
    simpa [hEq] using hφ₁st

  exact (hA φ).mpr hφst

-- ============================================================================
-- § 6. Identity laws (Isabelle's emp_star_right_id, emp_star_left_id)
-- ============================================================================

/-- `A ⊗ emp ⊢ A` — the `⊢` direction of `A ⊗ emp = A`. -/
theorem sep_emp_entails (A : Assertion) : A ∗ emp ⊢ A := by
  intro φ ⟨φ₁, φ₂, hplus, hA, ⟨b, hb⟩⟩
  rw [hb] at hplus
  have := VirtualState.stabilize_core_emp hplus
  grind

/-- `A ⊢ A ⊗ emp` — the `⊢` direction of `A = A ⊗ emp`. -/
theorem entails_sep_emp (A : Assertion) : A ⊢ A ∗ emp := by
  intro φ hA
  refine ⟨φ, VirtualState.empty, ?_, hA, ?_⟩
  · exact VirtualState.plus_empty_right φ
  · exact ⟨VirtualState.empty, (VirtualState.stabilize_core_eq_empty _).symm⟩

/-- `emp ⊗ A ⊢ A`. -/
theorem emp_sep_entails (A : Assertion) : emp ∗ A ⊢ A := by
  intro φ ⟨φ₁, φ₂, hplus, ⟨b, hb⟩, hA⟩
  rw [hb] at hplus
  have := VirtualState.stabilize_core_emp_left hplus
  grind

/-- `A ⊢ emp ⊗ A`. -/
theorem entails_emp_sep (A : Assertion) : A ⊢ emp ∗ A := by
  intro φ hA
  refine ⟨VirtualState.empty, φ, ?_, ?_, hA⟩
  · exact VirtualState.plus_empty_left φ
  · exact ⟨VirtualState.empty, (VirtualState.stabilize_core_eq_empty _).symm⟩

-- ============================================================================
-- § 7. Stable_emp and the status of self_framing emp
-- ============================================================================

/-- **`Stable emp`** (Isabelle `Stable_emp`): every state in emp has its stabilize in emp.

    This is the **one-way** property that CSL actually relies on. It holds
    unconditionally because the only element of emp is empty, and
    stabilize empty = empty. -/
theorem Stable_emp : ∀ φ, emp φ → emp (VirtualState.stabilize φ) := by
  intro φ hemp
  rw [emp_iff_empty] at hemp
  subst hemp
  rw [emp_iff_empty]
  -- stabilize empty = empty
  apply VirtualState.ext
  · intro hl; rfl
  · intro hl
    simp [VirtualState.stabilize, VirtualState.empty, preal.ppos]

/-- **`SelfFraming emp` holds on Stable states** — the honest status.

    The biconditional `P φ ↔ P (stabilize φ)` fails in general for `emp`,
    because a state with mask=0 everywhere but some garbage heap value
    has stabilize φ = empty (so the RHS holds) but φ ≠ empty (so the LHS doesn't).

    However, such states are *not Stable* (they have a heap value without permission).
    On Stable states, stabilize is the identity (by `stable_eq_stabilize`),
    so SelfFraming becomes trivial.

    This is the form in which Isabelle's CSL uses SelfFraming: CSL triples
    are restricted to Stable initial states. -/
theorem SelfFraming_emp_on_stable :
    ∀ φ, φ.Stable → (emp φ ↔ emp (VirtualState.stabilize φ)) := by
  intro φ hs
  rw [VirtualState.stable_eq_stabilize hs]

-- ============================================================================
-- § 8. Points-to assertions  (unchanged semantics from user's file)
-- ============================================================================

def acc (hl : HeapLoc) (p : preal) : Assertion :=
  fun φ => p.ppos ∧ p ≤ φ.mask hl

def fieldEq (hl : HeapLoc) (v : Val) : Assertion :=
  fun φ => φ.heap hl = some v

def pointsToDirect (hl : HeapLoc) (p : preal) (v : Val) : Assertion :=
  fun φ => p.ppos ∧ p ≤ φ.mask hl ∧ φ.heap hl = some v

def pointsToFrac (hl : HeapLoc) (p : preal) (v : Val) : Assertion :=
  acc hl p ∗ fieldEq hl v

def pointsTo (hl : HeapLoc) (v : Val) : Assertion :=
  pointsToDirect hl 1 v

theorem selfFraming_acc (hl : HeapLoc) (p : preal) :
    SelfFraming (acc hl p) := by
  intro φ; simp [acc, VirtualState.stabilize]

theorem selfFraming_pointsToDirect (hl : HeapLoc) (p : preal) (v : Val) :
    SelfFraming (pointsToDirect hl p v) := by
  intro φ
  constructor
  · intro ⟨hp, hle, hheap⟩
    have hppos : (φ.mask hl).ppos := by
      unfold preal.ppos at hp; unfold preal.ppos
      unfold LE.le at hle; unfold preal.instLE at hle; simp at hle
      grind
    refine ⟨hp, ?_, ?_⟩
    · simpa [VirtualState.stabilize] using hle
    · simpa [VirtualState.stabilize, hppos] using hheap
  · intro ⟨hp, hle, hheap⟩
    refine ⟨hp, ?_, ?_⟩
    · simpa [VirtualState.stabilize] using hle
    · have hppos : (φ.mask hl).ppos := by
        unfold preal.ppos at hp; unfold preal.ppos
        unfold LE.le at hle; unfold preal.instLE at hle; simp at hle
        grind
      simpa [VirtualState.stabilize, hppos] using hheap

theorem pointsToDirect_entails_acc (hl : HeapLoc) (p : preal) (v : Val) :
    pointsToDirect hl p v ⊢ acc hl p := fun _ h => ⟨h.1, h.2.1⟩

theorem pointsToDirect_entails_fieldEq (hl : HeapLoc) (p : preal) (v : Val) :
    pointsToDirect hl p v ⊢ fieldEq hl v := fun _ h => h.2.2

end Assertion



namespace Examples

open Assertion

def pf (pAddr : Address) : HeapLoc := ⟨pAddr, "f"⟩

def ex1 (pAddr : Address) : Assertion :=
  pointsToDirect (pf pAddr) 1 (Val.vInt 5)

def ex1_sep (pAddr : Address) : Assertion :=
  acc (pf pAddr) 1 ∗ fieldEq (pf pAddr) (Val.vInt 5)

theorem ex1_selfFraming (pAddr : Address) :
    SelfFraming (ex1 pAddr) := by
  simpa [ex1] using selfFraming_pointsToDirect (pf pAddr) 1 (Val.vInt 5)

end Examples
