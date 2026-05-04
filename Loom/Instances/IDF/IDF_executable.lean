import Std.Data.ExtTreeMap.Lemmas
import Loom.Instances.IDF.IDF_basic

open Std
set_option autoImplicit false

namespace IDFExecutable

instance : DecidableRel ((· ≤ ·) : preal → preal → Prop) :=
  fun a b => inferInstanceAs (Decidable (a.val ≤ b.val))

instance : DecidableRel ((· < ·) : preal → preal → Prop) :=
  fun a b => inferInstanceAs (Decidable (a.val < b.val))

@[simp] theorem preal.zero_add (a : preal) : 0 + a = a := by
  apply preal.ext
  simp [preal.add_val, Rat.zero_add]

@[simp] theorem preal.add_zero (a : preal) : a + 0 = a := by
  apply preal.ext
  simp [preal.add_val, Rat.add_zero]

@[simp] theorem preal.add_comm (a b : preal) : a + b = b + a := by
  apply preal.ext
  simp [preal.add_val, Rat.add_comm]

@[simp] theorem preal.add_assoc (a b c : preal) : a + b + c = a + (b + c) := by
  apply preal.ext
  simp only [preal.add_val]
  rw [Rat.add_assoc]

theorem preal.ppos_add_of_left {a b : preal} (ha : a.ppos) : (a + b).ppos := by
  unfold preal.ppos at *
  simp [preal.add_val]
  grind [a.nonneg, b.nonneg]

theorem preal.ppos_add_of_right {a b : preal} (hb : b.ppos) : (a + b).ppos := by
  rw [preal.add_comm]
  exact preal.ppos_add_of_left hb

theorem preal.eq_zero_of_not_ppos {a : preal} (ha : ¬ a.ppos) : a = 0 := by
  apply preal.ext
  unfold preal.ppos at ha
  exact le_antisymm ((Rat.not_lt).mp ha) a.nonneg

theorem preal.not_ppos_add {a b : preal} (ha : ¬ a.ppos) (hb : ¬ b.ppos) :
    ¬ (a + b).ppos := by
  rw [preal.eq_zero_of_not_ppos ha, preal.eq_zero_of_not_ppos hb]
  simp [preal.ppos]

def heapLocCompare : HeapLoc → HeapLoc → Ordering :=
  compareLex (compareOn HeapLoc.addr) (compareOn HeapLoc.field)

instance : ReflCmp heapLocCompare := by
  unfold heapLocCompare; infer_instance

instance : OrientedCmp heapLocCompare := by
  unfold heapLocCompare; infer_instance

instance : TransCmp heapLocCompare := by
  unfold heapLocCompare; infer_instance

instance : LawfulEqCmp heapLocCompare where
  eq_of_compare {a b} h := by
    cases a with
    | mk addr₁ field₁ =>
      cases b with
      | mk addr₂ field₂ =>
        simp [heapLocCompare, compareOn, compareLex_eq_eq, LawfulEqCmp.compare_eq_iff_eq] at h
        rcases h with ⟨hAddr, hField⟩
        cases hAddr
        cases hField
        rfl

instance : LawfulBEq HeapLoc where
  eq_of_beq {a b} h := by
    cases a with
    | mk addr₁ field₁ =>
      cases b with
      | mk addr₂ field₂ =>
        unfold instBEqHeapLoc instBEqHeapLoc.beq at h
        simp at h
        rcases h with ⟨hAddr, hField⟩
        cases hAddr
        cases hField
        rfl
  rfl {a} := by
    cases a with
    | mk addr field =>
      unfold instBEqHeapLoc instBEqHeapLoc.beq
      simp

instance : LawfulBEqCmp heapLocCompare where
  compare_eq_iff_beq := by
    intro a b
    rw [(LawfulEqCmp.compare_eq_iff_eq (cmp := heapLocCompare))]
    simpa using (beq_iff_eq (a := a) (b := b)).symm

abbrev Mask := ExtTreeMap HeapLoc preal heapLocCompare
abbrev PartialHeap := ExtTreeMap HeapLoc Val heapLocCompare

def wfMaskSimple (π : Mask) : Prop :=
  (π.keys.all fun hl =>
    match π.get? hl with
    | some v => decide (v ≤ 1)
    | none => true) = true

def wfHeapDom (π : Mask) (h : PartialHeap) : Prop :=
  (π.keys.all fun hl =>
    match π.get? hl with
    | some p => decide (p.ppos → (h.get? hl).isSome)
    | none => true) = true

def wfPreVirtualState (π : Mask) (h : PartialHeap) : Prop :=
  wfHeapDom π h ∧ wfMaskSimple π

instance instDecidableWfMaskSimple (π : Mask) : Decidable (wfMaskSimple π) := by
  unfold wfMaskSimple; infer_instance

instance instDecidableWfHeapDom (π : Mask) (h : PartialHeap) : Decidable (wfHeapDom π h) := by
  unfold wfHeapDom; infer_instance

instance instDecidableWfPreVirtualState (π : Mask) (h : PartialHeap) :
    Decidable (wfPreVirtualState π h) := by
  unfold wfPreVirtualState; infer_instance

structure VirtualState where
  mask : Mask
  heap : PartialHeap
  wf : wfPreVirtualState mask heap

namespace VirtualState

def empty : VirtualState where
  mask := ∅
  heap := ∅
  wf := by unfold wfPreVirtualState wfHeapDom wfMaskSimple; decide

instance : Inhabited VirtualState := ⟨empty⟩

def readField (φ : VirtualState) (hl : HeapLoc) : Option Val := φ.heap.get? hl

def getPerm (φ : VirtualState) (hl : HeapLoc) : preal := φ.mask.getD hl 0

def hasPerm (φ : VirtualState) (hl : HeapLoc) : Prop := (φ.getPerm hl).ppos

instance instDecidableHasPerm (φ : VirtualState) (hl : HeapLoc) :
    Decidable (φ.hasPerm hl) := by
  show Decidable ((φ.getPerm hl).ppos); infer_instance

def Stable (φ : VirtualState) : Prop :=
  (φ.heap.keys.all fun hl =>
    match φ.heap.get? hl with
    | some _ => decide ((φ.getPerm hl).ppos)
    | none => true) = true

instance instDecidableStable (φ : VirtualState) : Decidable φ.Stable := by
  unfold Stable; infer_instance

end VirtualState

def maskPlus (π₁ π₂ : Mask) : Mask :=
  π₂.foldl (fun acc hl p => acc.insert hl (acc.getD hl 0 + p)) π₁

def heapInsertIfCompatible (h : PartialHeap) (hl : HeapLoc) (v : Val) : Option PartialHeap :=
  match h.get? hl with
  | none => some (h.insert hl v)
  | some w => if w = v then some h else none

def heapCompatible (h₁ h₂ : PartialHeap) : Prop :=
  (h₁.keys.all fun hl =>
    match h₁.get? hl, h₂.get? hl with
    | some v₁, some v₂ => decide (v₁ = v₂)
    | _, _ => true) = true

instance instDecidableHeapCompatible (h₁ h₂ : PartialHeap) :
    Decidable (heapCompatible h₁ h₂) := by
  unfold heapCompatible; infer_instance

def heapMerge (h₁ h₂ : PartialHeap) : Option PartialHeap :=
  if _ : heapCompatible h₁ h₂ then some (h₁ ∪ h₂) else none

namespace VirtualState

def plus (a b : VirtualState) : Option VirtualState :=
  match heapMerge a.heap b.heap with
  | none => none
  | some heap =>
      let mask := maskPlus a.mask b.mask
      if hWF : wfPreVirtualState mask heap then
        some { mask := mask, heap := heap, wf := hWF }
      else none

def Disjoint (a b : VirtualState) : Prop := (plus a b).isSome = true

instance instDecidableDisjoint (a b : VirtualState) : Decidable (Disjoint a b) := by
  unfold Disjoint; infer_instance

end VirtualState

-- ============================================================================
-- § Characterization lemmas for maskPlus and heapMerge
-- These require induction over foldl on ExtTreeMap; proofs are deferred.
-- ============================================================================

private theorem exists_val_of_mem_map_fst {hl : HeapLoc} {l : List (HeapLoc × preal)} :
    hl ∈ l.map Prod.fst → ∃ p, (hl, p) ∈ l := by
  intro h
  induction l with
  | nil =>
    simp at h
  | cons a tl ih =>
    rcases a with ⟨k, p⟩
    simp only [List.map, List.mem_cons] at h
    rcases h with h | h
    · subst h
      exact ⟨p, by simp⟩
    · rcases ih h with ⟨p', hp'⟩
      exact ⟨p', by simp [hp']⟩

private theorem fold_maskPlus_list_getD_of_not_mem
    (l : List (HeapLoc × preal)) (π : Mask) (hl : HeapLoc)
    (hnot : hl ∉ l.map Prod.fst) :
    (l.foldl (fun acc p => acc.insert p.1 (acc.getD p.1 0 + p.2)) π).getD hl 0 = π.getD hl 0 := by
  induction l generalizing π with
  | nil =>
    rfl
  | cons a tl ih =>
    rcases a with ⟨k, v⟩
    simp only [List.map, List.mem_cons, not_or] at hnot
    have hkneq : heapLocCompare k hl ≠ .eq := by
      intro hk
      apply hnot.1
      exact ((LawfulEqCmp.compare_eq_iff_eq (cmp := heapLocCompare)).mp hk).symm
    have htlnot : hl ∉ tl.map Prod.fst := hnot.2
    rw [List.foldl_cons, ih (π := π.insert k (π.getD k 0 + v)) htlnot]
    rw [Std.ExtTreeMap.getD_insert]
    simp [hkneq]

private theorem not_mem_tail_of_pairwise_head_eq
    {k hl : HeapLoc} {tl : List (HeapLoc × preal)}
    (hhead : ∀ b ∈ tl, ¬ heapLocCompare k b.1 = .eq)
    (heq : heapLocCompare k hl = .eq) :
    hl ∉ tl.map Prod.fst := by
  intro hmem
  rcases exists_val_of_mem_map_fst hmem with ⟨p, hp⟩
  exact hhead (hl, p) hp heq

private theorem not_mem_map_fst_toList_of_getElem?_eq_none
    (π : Mask) (hl : HeapLoc) (hnone : π[hl]? = none) :
    hl ∉ π.toList.map Prod.fst := by
  intro hmem
  rcases exists_val_of_mem_map_fst hmem with ⟨p, hp⟩
  have hsome : π[hl]? = some p := by
    exact (Std.ExtTreeMap.getElem?_eq_some_iff_exists_compare_eq_eq_and_mem_toList
      (t := π) (k := hl) (v := p)).2
      ⟨hl, ReflCmp.compare_self (cmp := heapLocCompare), hp⟩
  rw [hnone] at hsome
  simp at hsome

private theorem getD_ofList_toList (π : Mask) (hl : HeapLoc) :
    (Std.ExtTreeMap.ofList π.toList heapLocCompare).getD hl 0 = π.getD hl 0 := by
  cases hget : π[hl]? with
  | none =>
    have hnot : hl ∉ π.toList.map Prod.fst := not_mem_map_fst_toList_of_getElem?_eq_none π hl hget
    have hof : (Std.ExtTreeMap.ofList π.toList heapLocCompare).getD hl 0 = 0 :=
      Std.ExtTreeMap.getD_ofList_of_contains_eq_false (by simpa [List.contains_eq_mem] using hnot)
    have hnotπ : ¬ hl ∈ π := by
      simpa [Std.ExtTreeMap.mem_iff_isSome_getElem?, hget]
    have hcontainsπ : π.contains hl = false := by
      simpa [Std.ExtTreeMap.contains_eq_isSome_getElem?, hget]
    have hpi : π.getD hl 0 = 0 := by
      exact Std.ExtTreeMap.getD_eq_fallback_of_contains_eq_false hcontainsπ
    rw [hof, hpi]
  | some p =>
    have hmem : hl ∈ π := (Std.ExtTreeMap.mem_iff_isSome_getElem?).mpr (by simp [hget])
    have hpi : π.getD hl 0 = p := by
      have := Std.ExtTreeMap.getElem?_eq_some_getD (t := π) (a := hl) (fallback := 0) hmem
      simpa [hget] using this.symm
    have hsome :
        (Std.ExtTreeMap.ofList π.toList heapLocCompare).getD hl 0 = p := by
      have hmem' : ∃ k, heapLocCompare hl k = .eq ∧ (k, p) ∈ π.toList :=
        (Std.ExtTreeMap.getElem?_eq_some_iff_exists_compare_eq_eq_and_mem_toList
          (t := π) (k := hl) (v := p)).1 hget
      rcases hmem' with ⟨k, hk, hpair⟩
      have hk' : heapLocCompare k hl = .eq := by
        exact (OrientedCmp.eq_comm (cmp := heapLocCompare) (a := k) (b := hl)).2 hk
      exact Std.ExtTreeMap.getD_ofList_of_mem hk'
        (Std.ExtTreeMap.distinct_keys_toList (t := π)) hpair
    rw [hsome, hpi]

private theorem fold_maskPlus_list_contains
    (l : List (HeapLoc × preal)) (π : Mask) (hl : HeapLoc) :
    (l.foldl (fun acc p => acc.insert p.1 (acc.getD p.1 0 + p.2)) π).contains hl =
      ((l.map Prod.fst).contains hl || π.contains hl) := by
  induction l generalizing π with
  | nil =>
    simp
  | cons a tl ih =>
    rcases a with ⟨k, v⟩
    rw [List.foldl_cons, ih (π := π.insert k (π.getD k 0 + v)), Std.ExtTreeMap.contains_insert]
    simp [List.contains_cons, LawfulBEqCmp.compare_beq_eq_beq (cmp := heapLocCompare), BEq.comm,
      Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem maskPlus_contains (π₁ π₂ : Mask) (hl : HeapLoc) :
    (maskPlus π₁ π₂).contains hl = (π₁.contains hl || π₂.contains hl) := by
  rw [maskPlus, Std.ExtTreeMap.foldl_eq_foldl_toList, fold_maskPlus_list_contains,
    Std.ExtTreeMap.map_fst_toList_eq_keys, Std.ExtTreeMap.contains_keys]
  simp [Bool.or_comm]

private theorem maskPlus_getD_list
    (l : List (HeapLoc × preal))
    (hdist : l.Pairwise (fun a b => ¬ heapLocCompare a.1 b.1 = .eq))
    (π : Mask) (hl : HeapLoc) :
    (l.foldl (fun acc p => acc.insert p.1 (acc.getD p.1 0 + p.2)) π).getD hl 0 =
      π.getD hl 0 + (Std.ExtTreeMap.ofList l heapLocCompare).getD hl 0 := by
  induction l generalizing π hl with
  | nil =>
    apply preal.ext
    exact (Rat.add_zero (ExtTreeMap.getD π hl 0).val).symm
  | cons a tl ih =>
    rcases a with ⟨k, v⟩
    have hpair := List.pairwise_cons.1 hdist
    have hhead : ∀ b ∈ tl, ¬ heapLocCompare k b.1 = .eq := by
      simpa using hpair.1
    have htail : tl.Pairwise (fun a b => ¬ heapLocCompare a.1 b.1 = .eq) := by
      simpa using hpair.2
    by_cases heq : heapLocCompare k hl = .eq
    · have hnot : hl ∉ tl.map Prod.fst := not_mem_tail_of_pairwise_head_eq hhead heq
      have hfold :
          (tl.foldl (fun acc p => acc.insert p.1 (acc.getD p.1 0 + p.2))
            (π.insert k (π.getD k 0 + v))).getD hl 0 =
          (π.insert k (π.getD k 0 + v)).getD hl 0 :=
        fold_maskPlus_list_getD_of_not_mem tl (π.insert k (π.getD k 0 + v)) hl hnot
      have hof : (Std.ExtTreeMap.ofList ((k, v) :: tl) heapLocCompare).getD hl 0 = v :=
        Std.ExtTreeMap.getD_ofList_of_mem heq hdist (by simp)
      have hcongr : π.getD k 0 = π.getD hl 0 := Std.ExtTreeMap.getD_congr heq
      rw [List.foldl_cons, hfold, Std.ExtTreeMap.getD_insert, hof]
      simp [heq, hcongr]
    · have hstep : (π.insert k (π.getD k 0 + v)).getD hl 0 = π.getD hl 0 := by
        rw [Std.ExtTreeMap.getD_insert]
        simp [heq]
      have hof :
          (Std.ExtTreeMap.ofList ((k, v) :: tl) heapLocCompare).getD hl 0 =
          (Std.ExtTreeMap.ofList tl heapLocCompare).getD hl 0 := by
        by_cases hmem : hl ∈ tl.map Prod.fst
        · rcases exists_val_of_mem_map_fst hmem with ⟨p, hp⟩
          have hcons :
              (Std.ExtTreeMap.ofList ((k, v) :: tl) heapLocCompare).getD hl 0 = p :=
            Std.ExtTreeMap.getD_ofList_of_mem
              ((LawfulEqCmp.compare_eq_iff_eq (cmp := heapLocCompare)).mpr rfl) hdist (by simp [hp])
          have htail' :
              (Std.ExtTreeMap.ofList tl heapLocCompare).getD hl 0 = p :=
            Std.ExtTreeMap.getD_ofList_of_mem
              ((LawfulEqCmp.compare_eq_iff_eq (cmp := heapLocCompare)).mpr rfl) htail hp
          rw [hcons, htail']
        · have hcontainsTl : (tl.map Prod.fst).contains hl = false := by
            simpa [List.contains_eq_mem] using hmem
          have hkneq : k ≠ hl := by
            intro hEq
            apply heq
            simpa [hEq] using (((LawfulEqCmp.compare_eq_iff_eq (cmp := heapLocCompare)).mpr rfl) :
              heapLocCompare hl hl = .eq)
          have hnotCons : hl ∉ ((k, v) :: tl).map Prod.fst := by
            intro hmemCons
            simp only [List.map, List.mem_cons] at hmemCons
            rcases hmemCons with hEq | hIn
            · exact hkneq hEq.symm
            · exact hmem hIn
          have hcontainsCons : (((k, v) :: tl).map Prod.fst).contains hl = false := by
            simpa [List.contains_eq_mem] using hnotCons
          have hcons :
              (Std.ExtTreeMap.ofList ((k, v) :: tl) heapLocCompare).getD hl 0 = 0 :=
            Std.ExtTreeMap.getD_ofList_of_contains_eq_false hcontainsCons
          have htail' :
              (Std.ExtTreeMap.ofList tl heapLocCompare).getD hl 0 = 0 :=
            Std.ExtTreeMap.getD_ofList_of_contains_eq_false hcontainsTl
          rw [hcons, htail']
      rw [List.foldl_cons, ih htail (π := π.insert k (π.getD k 0 + v)) (hl := hl), hstep, hof]

/-- `maskPlus` acts pointwise: permission at any location is the sum. -/
theorem maskPlus_getD (π₁ π₂ : Mask) (hl : HeapLoc) :
    (maskPlus π₁ π₂).getD hl 0 = π₁.getD hl 0 + π₂.getD hl 0 := by
  rw [maskPlus, Std.ExtTreeMap.foldl_eq_foldl_toList]
  rw [maskPlus_getD_list π₂.toList (Std.ExtTreeMap.distinct_keys_toList (t := π₂)) π₁ hl]
  rw [getD_ofList_toList]

private theorem maskPlus_comm (π₁ π₂ : Mask) : maskPlus π₁ π₂ = maskPlus π₂ π₁ := by
  refine Std.ExtTreeMap.ext_getElem? ?_
  intro hl
  by_cases hcont : (maskPlus π₁ π₂).contains hl = true
  · have hcont' : (maskPlus π₂ π₁).contains hl = true := by
      rw [maskPlus_contains] at hcont ⊢
      simpa [Bool.or_comm] using hcont
    have hleft0 := Std.ExtTreeMap.getElem?_eq_some_getD_of_contains
      (t := maskPlus π₁ π₂) (a := hl) (fallback := 0) hcont
    have hright0 := Std.ExtTreeMap.getElem?_eq_some_getD_of_contains
      (t := maskPlus π₂ π₁) (a := hl) (fallback := 0) hcont'
    have hleft : (maskPlus π₁ π₂)[hl]? = some (π₁.getD hl 0 + π₂.getD hl 0) := by
      simpa [maskPlus_getD] using hleft0
    have hright : (maskPlus π₂ π₁)[hl]? = some (π₂.getD hl 0 + π₁.getD hl 0) := by
      simpa [maskPlus_getD] using hright0
    have hright' : (maskPlus π₂ π₁)[hl]? = some (π₁.getD hl 0 + π₂.getD hl 0) := by
      simpa [preal.add_comm] using hright
    exact hleft.trans hright'.symm
  · have hcontF : (maskPlus π₁ π₂).contains hl = false := by
      cases hc : (maskPlus π₁ π₂).contains hl <;> simp [hc] at hcont ⊢
    have hcont' : (maskPlus π₂ π₁).contains hl = false := by
      rw [maskPlus_contains] at hcontF ⊢
      simpa [Bool.or_comm] using hcontF
    rw [Std.ExtTreeMap.getElem?_eq_none_of_contains_eq_false hcontF,
      Std.ExtTreeMap.getElem?_eq_none_of_contains_eq_false hcont']

private theorem maskPlus_assoc (π₁ π₂ π₃ : Mask) :
    maskPlus (maskPlus π₁ π₂) π₃ = maskPlus π₁ (maskPlus π₂ π₃) := by
  refine Std.ExtTreeMap.ext_getElem? ?_
  intro hl
  by_cases hcont : (maskPlus (maskPlus π₁ π₂) π₃).contains hl = true
  · have hcont' : (maskPlus π₁ (maskPlus π₂ π₃)).contains hl = true := by
      rw [maskPlus_contains, maskPlus_contains] at hcont ⊢
      simpa [Bool.or_assoc] using hcont
    have hleft0 := Std.ExtTreeMap.getElem?_eq_some_getD_of_contains
      (t := maskPlus (maskPlus π₁ π₂) π₃) (a := hl) (fallback := 0) hcont
    have hright0 := Std.ExtTreeMap.getElem?_eq_some_getD_of_contains
      (t := maskPlus π₁ (maskPlus π₂ π₃)) (a := hl) (fallback := 0) hcont'
    have hleft : (maskPlus (maskPlus π₁ π₂) π₃)[hl]? =
        some (π₁.getD hl 0 + π₂.getD hl 0 + π₃.getD hl 0) := by
      simpa [maskPlus_getD, preal.add_assoc] using hleft0
    have hright : (maskPlus π₁ (maskPlus π₂ π₃))[hl]? =
        some (π₁.getD hl 0 + (π₂.getD hl 0 + π₃.getD hl 0)) := by
      simpa [maskPlus_getD] using hright0
    have hright' : (maskPlus π₁ (maskPlus π₂ π₃))[hl]? =
        some (π₁.getD hl 0 + π₂.getD hl 0 + π₃.getD hl 0) := by
      simpa [preal.add_assoc] using hright
    exact hleft.trans hright'.symm
  · have hcontF : (maskPlus (maskPlus π₁ π₂) π₃).contains hl = false := by
      cases hc : (maskPlus (maskPlus π₁ π₂) π₃).contains hl <;> simp [hc] at hcont ⊢
    have hcont' : (maskPlus π₁ (maskPlus π₂ π₃)).contains hl = false := by
      rw [maskPlus_contains, maskPlus_contains] at hcontF ⊢
      simpa [Bool.or_assoc] using hcontF
    rw [Std.ExtTreeMap.getElem?_eq_none_of_contains_eq_false hcontF,
      Std.ExtTreeMap.getElem?_eq_none_of_contains_eq_false hcont']

/-- When `heapMerge` succeeds and `h₁` has a value at `hl`, the result carries it. -/
theorem heapMerge_get?_of_left {h₁ h₂ h : PartialHeap} {hl : HeapLoc} {v : Val}
    (hm : heapMerge h₁ h₂ = some h) (h1 : h₁.get? hl = some v) :
    h.get? hl = some v := by
  by_cases hc : heapCompatible h₁ h₂
  · have hm' : some (h₁ ∪ h₂) = some h := by
        simpa [heapMerge, hc] using hm
    have hh : h = h₁ ∪ h₂ := Option.some.inj hm'.symm
    subst hh
    change (h₁ ∪ h₂)[hl]? = some v
    cases h2 : h₂.get? hl with
    | none =>
      have hnotmem : ¬ hl ∈ h₂ := by
        intro hmem
        have his : h₂.get? hl = some (h₂.get hl hmem) := Std.ExtTreeMap.getElem?_eq_some_getElem hmem
        rw [h2] at his
        simp at his
      rw [Std.ExtTreeMap.getElem?_union_of_not_mem_right hnotmem]
      exact h1
    | some v₂ =>
      have hmem : hl ∈ h₁ := (Std.ExtTreeMap.mem_iff_isSome_getElem?).mpr (Option.isSome_of_eq_some h1)
      have hkeys : hl ∈ h₁.keys := (Std.ExtTreeMap.mem_keys).mpr hmem
      have hchk := (List.all_eq_true.mp hc) hl hkeys
      rw [h1, h2] at hchk
      have hv : v = v₂ := by simpa using hchk
      have h1' : h₁[hl]? = some v := by simpa using h1
      have h2' : h₂[hl]? = some v₂ := by simpa using h2
      have hu := Std.ExtTreeMap.getElem?_union (t₁ := h₁) (t₂ := h₂) (k := hl)
      rw [h2', h1'] at hu
      simpa [hv] using hu
  · have hm' : none = some h := by
        simpa [heapMerge, hc] using hm
    simp at hm'

/-- When `heapMerge` succeeds and `h₁` has no entry, the result agrees with `h₂`. -/
theorem heapMerge_get?_of_none {h₁ h₂ h : PartialHeap} {hl : HeapLoc}
    (hm : heapMerge h₁ h₂ = some h) (h1 : h₁.get? hl = none) :
    h.get? hl = h₂.get? hl := by
  by_cases hc : heapCompatible h₁ h₂
  · have hm' : some (h₁ ∪ h₂) = some h := by
        simpa [heapMerge, hc] using hm
    have hh : h = h₁ ∪ h₂ := Option.some.inj hm'.symm
    subst hh
    have hnotmem : ¬ hl ∈ h₁ := by
      intro hmem
      have his : h₁.get? hl = some (h₁.get hl hmem) := Std.ExtTreeMap.getElem?_eq_some_getElem hmem
      rw [h1] at his
      simp at his
    exact Std.ExtTreeMap.getElem?_union_of_not_mem_left hnotmem
  · have hm' : none = some h := by
        simpa [heapMerge, hc] using hm
    simp at hm'

/-- `heapMerge` succeeds iff the heaps have no conflicting values. -/
theorem heapMerge_isSome_iff {h₁ h₂ : PartialHeap} :
    (heapMerge h₁ h₂).isSome ↔ heapCompatible h₁ h₂ := by
  unfold heapMerge
  by_cases hc : heapCompatible h₁ h₂ <;> simp [hc]

/-- `heapCompatible` is equivalent to the pointwise ∀-formulation. -/
theorem heapCompatible_iff_forall {h₁ h₂ : PartialHeap} :
    heapCompatible h₁ h₂ ↔
    ∀ hl v₁ v₂, h₁.get? hl = some v₁ → h₂.get? hl = some v₂ → v₁ = v₂ := by
  constructor
  · intro hc hl v₁ v₂ h1 h2
    have hmem : hl ∈ h₁ := (Std.ExtTreeMap.mem_iff_isSome_getElem?).mpr (Option.isSome_of_eq_some h1)
    have hkeys : hl ∈ h₁.keys := (Std.ExtTreeMap.mem_keys).mpr hmem
    have hchk := (List.all_eq_true.mp hc) hl hkeys
    rw [h1, h2] at hchk
    simp at hchk
    exact hchk
  · intro hforall
    unfold heapCompatible
    rw [List.all_eq_true]
    intro hl hkeys
    have hmem : hl ∈ h₁ := (Std.ExtTreeMap.mem_keys).mp hkeys
    have h1 : h₁.get? hl = some (h₁.get hl hmem) := Std.ExtTreeMap.getElem?_eq_some_getElem hmem
    cases h2 : h₂.get? hl with
    | none =>
      rw [h1]
    | some v₂ =>
      have hv : h₁.get hl hmem = v₂ := hforall hl _ _ h1 h2
      rw [h1]
      simpa using hv

theorem heapCompatible_symm {h₁ h₂ : PartialHeap} (h : heapCompatible h₁ h₂) :
    heapCompatible h₂ h₁ := by
  rw [heapCompatible_iff_forall] at *
  exact fun hl v₁ v₂ h2 h1 => (h hl v₂ v₁ h1 h2).symm

private theorem heapUnion_comm_of_compatible {h₁ h₂ : PartialHeap}
    (hc : heapCompatible h₁ h₂) : h₁ ∪ h₂ = h₂ ∪ h₁ := by
  refine Std.ExtTreeMap.ext_getElem? ?_
  intro hl
  cases h1 : h₁.get? hl with
  | none =>
    have hnotmem : ¬ hl ∈ h₁ := by
      intro hmem
      have his : h₁.get? hl = some (h₁.get hl hmem) := Std.ExtTreeMap.getElem?_eq_some_getElem hmem
      rw [h1] at his
      simp at his
    rw [Std.ExtTreeMap.getElem?_union_of_not_mem_left hnotmem,
      Std.ExtTreeMap.getElem?_union_of_not_mem_right hnotmem]
  | some v1 =>
    cases h2 : h₂.get? hl with
    | none =>
      have hnotmem : ¬ hl ∈ h₂ := by
        intro hmem
        have his : h₂.get? hl = some (h₂.get hl hmem) := Std.ExtTreeMap.getElem?_eq_some_getElem hmem
        rw [h2] at his
        simp at his
      rw [Std.ExtTreeMap.getElem?_union_of_not_mem_right hnotmem,
        Std.ExtTreeMap.getElem?_union_of_not_mem_left hnotmem]
    | some v2 =>
      have hv : v1 = v2 := (heapCompatible_iff_forall.mp hc) hl v1 v2 h1 h2
      have hu12 := Std.ExtTreeMap.getElem?_union (t₁ := h₁) (t₂ := h₂) (k := hl)
      have hu21 := Std.ExtTreeMap.getElem?_union (t₁ := h₂) (t₂ := h₁) (k := hl)
      have h1' : h₁[hl]? = some v1 := by simpa using h1
      have h2' : h₂[hl]? = some v2 := by simpa using h2
      rw [h2', h1'] at hu12
      rw [h1', h2'] at hu21
      have hu12' : (h₁ ∪ h₂)[hl]? = some v1 := by simpa [hv] using hu12
      have hu21' : (h₂ ∪ h₁)[hl]? = some v1 := by simpa [hv] using hu21
      exact hu12'.trans hu21'.symm

private theorem heapUnion_assoc (h₁ h₂ h₃ : PartialHeap) :
    (h₁ ∪ h₂) ∪ h₃ = h₁ ∪ (h₂ ∪ h₃) := by
  refine Std.ExtTreeMap.ext_getElem? ?_
  intro hl
  rw [Std.ExtTreeMap.getElem?_union, Std.ExtTreeMap.getElem?_union,
    Std.ExtTreeMap.getElem?_union, Std.ExtTreeMap.getElem?_union]
  simp [Option.or_assoc]

private theorem heapMerge_comm {h₁ h₂ h : PartialHeap}
    (hm : heapMerge h₁ h₂ = some h) : heapMerge h₂ h₁ = some h := by
  have his : (heapMerge h₁ h₂).isSome := Option.isSome_of_eq_some hm
  have hc : heapCompatible h₁ h₂ := heapMerge_isSome_iff.mp his
  have hm' : some (h₁ ∪ h₂) = some h := by
    simpa [heapMerge, hc] using hm
  have hh : h = h₁ ∪ h₂ := Option.some.inj hm'.symm
  have hc' : heapCompatible h₂ h₁ := heapCompatible_symm hc
  rw [hh, heapUnion_comm_of_compatible hc]
  simp [heapMerge, hc']

theorem heapMerge_of_compatible {h₁ h₂ : PartialHeap} (hc : heapCompatible h₁ h₂) :
    ∃ h, heapMerge h₁ h₂ = some h :=
  Option.isSome_iff_exists.mp (heapMerge_isSome_iff.mpr hc)

-- ============================================================================
-- § VirtualState structural lemmas
-- ============================================================================

namespace VirtualState

theorem ext {a b : VirtualState} (hm : a.mask = b.mask) (hh : a.heap = b.heap) : a = b := by
  obtain ⟨am, ah, awf⟩ := a; obtain ⟨bm, bh, bwf⟩ := b
  simp only at hm hh; subst hm; subst hh
  have : awf = bwf := Subsingleton.elim _ _
  cases this
  rfl

private theorem heap_isSome_of_ppos {φ : VirtualState} {hl : HeapLoc}
    (hp : (φ.mask.getD hl 0).ppos) : (φ.heap.get? hl).isSome := by
  have hmem : hl ∈ φ.mask := by
    cases hc : φ.mask.contains hl with
    | false =>
      have hzero : φ.mask.getD hl 0 = 0 :=
        Std.ExtTreeMap.getD_eq_fallback_of_contains_eq_false hc
      rw [hzero] at hp
      simp [preal.ppos] at hp
    | true =>
      exact (Std.ExtTreeMap.mem_iff_contains).2 hc
  have hkey : hl ∈ φ.mask.keys := (Std.ExtTreeMap.mem_keys).2 hmem
  have hmask : φ.mask.get? hl = some (φ.mask.getD hl 0) :=
    Std.ExtTreeMap.getElem?_eq_some_getD hmem
  have hdom := (List.all_eq_true.mp φ.wf.1) hl hkey
  rw [hmask] at hdom
  simpa [hp] using hdom

/-- Unwrap `plus a b = some x` to get mask equality. -/
theorem plus_mask_getD {a b x : VirtualState} (h : plus a b = some x) (hl : HeapLoc) :
    x.mask.getD hl 0 = a.mask.getD hl 0 + b.mask.getD hl 0 := by
  unfold plus at h
  cases hm : heapMerge a.heap b.heap with
  | none => simp [hm] at h
  | some heap =>
    simp only [hm] at h
    by_cases hwf : wfPreVirtualState (maskPlus a.mask b.mask) heap
    · rw [dif_pos hwf] at h
      have hx : x = ⟨maskPlus a.mask b.mask, heap, hwf⟩ := Option.some.inj h.symm
      simp only [hx]; exact maskPlus_getD a.mask b.mask hl
    · rw [dif_neg hwf] at h; simp at h

private theorem plus_mask_eq {a b x : VirtualState} (h : plus a b = some x) :
    x.mask = maskPlus a.mask b.mask := by
  unfold plus at h
  cases hm : heapMerge a.heap b.heap with
  | none =>
    simp [hm] at h
  | some heap =>
    simp only [hm] at h
    by_cases hwf : wfPreVirtualState (maskPlus a.mask b.mask) heap
    · rw [dif_pos hwf] at h
      exact (congrArg VirtualState.mask (Option.some.inj h)).symm
    · rw [dif_neg hwf] at h
      simp at h

private theorem plus_heapMerge_eq {a b x : VirtualState} (h : plus a b = some x) :
    heapMerge a.heap b.heap = some x.heap := by
  unfold plus at h
  cases hm : heapMerge a.heap b.heap with
  | none =>
    simp [hm] at h
  | some heap =>
    simp only [hm] at h
    by_cases hwf : wfPreVirtualState (maskPlus a.mask b.mask) heap
    · rw [dif_pos hwf] at h
      exact congrArg VirtualState.heap (Option.some.inj h) |> congrArg some
    · rw [dif_neg hwf] at h
      simp at h

theorem plus_heap_of_left {a b x : VirtualState} (h : plus a b = some x)
    {hl : HeapLoc} {v : Val} (ha : a.heap.get? hl = some v) :
    x.heap.get? hl = some v := by
  unfold plus at h
  cases hm : heapMerge a.heap b.heap with
  | none => simp [hm] at h
  | some heap =>
    simp only [hm] at h
    by_cases hwf : wfPreVirtualState (maskPlus a.mask b.mask) heap
    · rw [dif_pos hwf] at h
      have hx : x = ⟨maskPlus a.mask b.mask, heap, hwf⟩ := Option.some.inj h.symm
      simp only [hx]; exact heapMerge_get?_of_left hm ha
    · rw [dif_neg hwf] at h; simp at h

theorem plus_heap_of_none {a b x : VirtualState} (h : plus a b = some x)
    {hl : HeapLoc} (ha : a.heap.get? hl = none) :
    x.heap.get? hl = b.heap.get? hl := by
  unfold plus at h
  cases hm : heapMerge a.heap b.heap with
  | none => simp [hm] at h
  | some heap =>
    simp only [hm] at h
    by_cases hwf : wfPreVirtualState (maskPlus a.mask b.mask) heap
    · rw [dif_pos hwf] at h
      have hx : x = ⟨maskPlus a.mask b.mask, heap, hwf⟩ := Option.some.inj h.symm
      simp only [hx]; exact heapMerge_get?_of_none hm ha
    · rw [dif_neg hwf] at h; simp at h

theorem plus_heap_of_right {a b x : VirtualState} (h : plus a b = some x)
    {hl : HeapLoc} {v : Val} (hb : b.heap.get? hl = some v) :
    x.heap.get? hl = some v := by
  have hm : heapMerge a.heap b.heap = some x.heap := plus_heapMerge_eq h
  have hm' : heapMerge b.heap a.heap = some x.heap := heapMerge_comm hm
  exact heapMerge_get?_of_left hm' hb

private theorem plus_comm {a b x : VirtualState} (h : plus a b = some x) :
    plus b a = some x := by
  have hm : heapMerge b.heap a.heap = some x.heap := heapMerge_comm (plus_heapMerge_eq h)
  have hmask : x.mask = maskPlus b.mask a.mask := by
    rw [plus_mask_eq h, maskPlus_comm]
  have hwf : wfPreVirtualState (maskPlus b.mask a.mask) x.heap := by
    simpa [hmask] using x.wf
  unfold plus
  rw [hm]
  simp [hwf]
  exact VirtualState.ext hmask.symm rfl

theorem disjoint_of_plus {a b x : VirtualState} (h : plus a b = some x) : Disjoint a b := by
  unfold Disjoint; simp [h]

-- ============================================================================
-- § stabilize and core
-- ============================================================================

private def filteredHeap (φ : VirtualState) : PartialHeap :=
  φ.heap.filter fun hl _ => (φ.mask.getD hl 0).ppos

/-- Key characterization of the stabilized heap. -/
private theorem filteredHeap_get? (φ : VirtualState) (hl : HeapLoc) :
    (filteredHeap φ).get? hl =
    if (φ.mask.getD hl 0).ppos then φ.heap.get? hl else none := by
  calc
    (filteredHeap φ).get? hl
      = (φ.heap.get? hl).filter (fun _ => decide ((φ.mask.getD hl 0).ppos)) := by
          simpa [filteredHeap] using
            (Std.ExtTreeMap.getElem?_filter' (t := φ.heap)
              (f := fun hl _ => decide ((φ.mask.getD hl 0).ppos)) (k := hl))
    _ = if (φ.mask.getD hl 0).ppos then φ.heap.get? hl else none := by
          by_cases hp : (φ.mask.getD hl 0).ppos
          · cases hheap : φ.heap.get? hl <;> simp [hp, hheap, Option.filter]
          · cases hheap : φ.heap.get? hl <;> simp [hp, hheap, Option.filter]

def stabilize (φ : VirtualState) : VirtualState where
  mask := φ.mask
  heap := filteredHeap φ
  wf := by
    constructor
    · unfold wfHeapDom
      rw [List.all_eq_true]
      intro hl hmem
      have hmaskmem : hl ∈ φ.mask := (Std.ExtTreeMap.mem_keys).mp hmem
      have hmask : φ.mask.get? hl = some (φ.mask.getD hl 0) :=
        Std.ExtTreeMap.getElem?_eq_some_getD hmaskmem
      by_cases hp : (φ.mask.getD hl 0).ppos
      · have hdom := (List.all_eq_true.mp φ.wf.1) hl hmem
        rw [hmask] at hdom
        simp [hp] at hdom
        rw [filteredHeap_get?]
        rw [hmask]
        simp [hp, hdom]
      · rw [hmask]
        simp [hp]
    · exact φ.wf.2

def core (φ : VirtualState) : VirtualState where
  mask := ∅
  heap := φ.heap
  wf := by
    unfold wfPreVirtualState wfHeapDom wfMaskSimple
    simp

@[simp] theorem stabilize_mask (φ : VirtualState) : (stabilize φ).mask = φ.mask := rfl
@[simp] theorem core_mask (φ : VirtualState) : (core φ).mask = ∅ := rfl
@[simp] theorem core_heap (φ : VirtualState) : (core φ).heap = φ.heap := rfl

theorem stabilize_heap_get? (φ : VirtualState) (hl : HeapLoc) :
    (stabilize φ).heap.get? hl =
    if (φ.mask.getD hl 0).ppos then φ.heap.get? hl else none :=
  filteredHeap_get? φ hl

-- ============================================================================
-- § Stable theorems
-- ============================================================================

/-- The computable `Stable` is equivalent to the universal ∀-formulation. -/
theorem stable_iff_forall (φ : VirtualState) :
    φ.Stable ↔ ∀ hl v, φ.heap.get? hl = some v → (φ.mask.getD hl 0).ppos := by
  unfold VirtualState.Stable
  constructor
  · intro hs hl v hget
    have hmem : hl ∈ φ.heap :=
      (Std.ExtTreeMap.mem_iff_isSome_getElem?).mpr (Option.isSome_of_eq_some hget)
    have hs' := (List.all_eq_true.mp hs) hl ((Std.ExtTreeMap.mem_keys).mpr hmem)
    rw [hget] at hs'
    simpa [VirtualState.getPerm] using hs'
  · intro hs
    rw [List.all_eq_true]
    intro hl hmem
    have hheapmem : hl ∈ φ.heap := (Std.ExtTreeMap.mem_keys).mp hmem
    have hget : φ.heap.get? hl = some (φ.heap.get hl hheapmem) :=
      Std.ExtTreeMap.getElem?_eq_some_getElem hheapmem
    rw [hget]
    simpa [VirtualState.getPerm] using hs hl _ hget

theorem stabilize_stable (φ : VirtualState) : (stabilize φ).Stable := by
  rw [stable_iff_forall]
  intro hl v hget
  rw [stabilize_heap_get?] at hget
  by_cases hp : (φ.mask.getD hl 0).ppos
  · simpa [VirtualState.getPerm, stabilize_mask, hp] using hp
  · simp [hp] at hget

theorem stable_eq_stabilize {φ : VirtualState} (hs : φ.Stable) : stabilize φ = φ := by
  refine VirtualState.ext rfl ?_
  rw [stable_iff_forall] at hs
  refine Std.ExtTreeMap.ext_getElem? ?_
  intro hl
  change (stabilize φ).heap.get? hl = φ.heap.get? hl
  rw [stabilize_heap_get?]
  by_cases hp : (φ.mask.getD hl 0).ppos
  · simp [hp]
  · cases hget : φ.heap.get? hl with
    | none => simp [hp, hget]
    | some v =>
      exact absurd (hs hl v hget) hp

theorem stable_of_eq_stabilize {φ : VirtualState} (h : stabilize φ = φ) : φ.Stable := by
  rw [stable_iff_forall]
  intro hl v hget
  have h' : (stabilize φ).heap.get? hl = φ.heap.get? hl := by
    simpa using congrArg (fun s => s.heap.get? hl) h
  rw [stabilize_heap_get?] at h'
  by_cases hp : (φ.mask.getD hl 0).ppos
  · exact hp
  · simp [hp] at h'
    have hmem : hl ∈ φ.heap :=
      (Std.ExtTreeMap.mem_iff_isSome_getElem?).mpr (Option.isSome_of_eq_some hget)
    exact False.elim (h' hmem)

-- ============================================================================
-- § heapMerge compatibility theorems (adapted from IDF_basic)
-- ============================================================================

theorem heapMerge_eq_left_of_compatible
    {h₁ h₂ h : PartialHeap} {hl : HeapLoc} {v : Val}
    (_hcomp : heapCompatible h₁ h₂) (hm : heapMerge h₁ h₂ = some h)
    (h1 : h₁.get? hl = some v) : h.get? hl = some v :=
  heapMerge_get?_of_left hm h1

theorem heapMerge_eq_right_of_compatible
    {h₁ h₂ h : PartialHeap} {hl : HeapLoc} {v : Val}
    (hcomp : heapCompatible h₁ h₂) (hm : heapMerge h₁ h₂ = some h)
    (h2 : h₂.get? hl = some v) : h.get? hl = some v := by
  cases h1 : h₁.get? hl with
  | none => rw [heapMerge_get?_of_none hm h1]; exact h2
  | some v₁ =>
    rw [heapMerge_get?_of_left hm h1]
    exact congrArg some ((heapCompatible_iff_forall.mp hcomp) hl v₁ v h1 h2)

-- ============================================================================
-- § plus: identity and sep-algebra axioms
-- ============================================================================

private theorem maskPlus_empty_left (π : Mask) : maskPlus ∅ π = π := by
  refine Std.ExtTreeMap.ext_getElem? ?_
  intro hl
  by_cases hcont : π.contains hl = true
  · have hmem : hl ∈ π := by
      exact (Std.ExtTreeMap.mem_iff_contains).2 (by simpa using hcont)
    have hkeys : (π.toList.map Prod.fst).contains hl = true := by
      have hkeymem : hl ∈ π.keys := (Std.ExtTreeMap.mem_keys).2 hmem
      rw [Std.ExtTreeMap.map_fst_toList_eq_keys]
      simpa [List.contains_eq_mem] using hkeymem
    have hcont' : (maskPlus ∅ π).contains hl = true := by
      rw [maskPlus, Std.ExtTreeMap.foldl_eq_foldl_toList, fold_maskPlus_list_contains]
      rw [hkeys, Std.ExtTreeMap.contains_empty]
      rfl
    have hleft := Std.ExtTreeMap.getElem?_eq_some_getD_of_contains
      (t := maskPlus ∅ π) (a := hl) (fallback := 0) hcont'
    have hright := Std.ExtTreeMap.getElem?_eq_some_getD_of_contains
      (t := π) (a := hl) (fallback := 0) hcont
    rw [maskPlus_getD, Std.ExtTreeMap.getD_empty] at hleft
    have hleft' : (maskPlus ∅ π)[hl]? = some (π.getD hl 0) := by
      simpa using hleft
    exact hleft'.trans hright.symm
  · have hcontF : π.contains hl = false := by
      cases hc : π.contains hl <;> simp [hc] at hcont ⊢
    have hnotmem : ¬ hl ∈ π := by
      intro hmem
      have hmem' : π.contains hl := (Std.ExtTreeMap.mem_iff_contains).1 hmem
      rw [hcontF] at hmem'
      simp at hmem'
    have hkeys : (π.toList.map Prod.fst).contains hl = false := by
      have hkeynot : ¬ hl ∈ π.keys := by simpa [Std.ExtTreeMap.mem_keys] using hnotmem
      rw [Std.ExtTreeMap.map_fst_toList_eq_keys]
      simpa [List.contains_eq_mem] using hkeynot
    have hcont' : (maskPlus ∅ π).contains hl = false := by
      rw [maskPlus, Std.ExtTreeMap.foldl_eq_foldl_toList, fold_maskPlus_list_contains]
      rw [hkeys, Std.ExtTreeMap.contains_empty]
      rfl
    rw [Std.ExtTreeMap.getElem?_eq_none_of_contains_eq_false hcont',
      Std.ExtTreeMap.getElem?_eq_none_of_contains_eq_false hcontF]

private theorem maskPlus_empty_right (π : Mask) : maskPlus π ∅ = π := by
  rfl

private theorem heapMerge_empty_left (h : PartialHeap) :
    ∃ r, heapMerge ∅ h = some r ∧ r = h := by
  refine ⟨h, ?_, rfl⟩
  have hunion : (∅ : PartialHeap) ∪ h = h := by
    refine Std.ExtTreeMap.ext_getElem? ?_
    intro hl
    exact Std.ExtTreeMap.getElem?_union_of_not_mem_left (by simp : ¬ hl ∈ (∅ : PartialHeap))
  unfold heapMerge heapCompatible
  simp [hunion]

private theorem heapMerge_empty_right (h : PartialHeap) :
    ∃ r, heapMerge h ∅ = some r ∧ r = h := by
  refine ⟨h, ?_, rfl⟩
  have hunion : h ∪ (∅ : PartialHeap) = h := by
    refine Std.ExtTreeMap.ext_getElem? ?_
    intro hl
    exact Std.ExtTreeMap.getElem?_union_of_not_mem_right (by simp : ¬ hl ∈ (∅ : PartialHeap))
  unfold heapMerge heapCompatible
  simp [hunion]

@[simp] theorem plus_empty_left (a : VirtualState) : plus empty a = some a := by
  unfold plus empty
  obtain ⟨h, hm, hheq⟩ := heapMerge_empty_left a.heap
  simp only [hm, maskPlus_empty_left, hheq, dif_pos a.wf]

@[simp] theorem plus_empty_right (a : VirtualState) : plus a empty = some a := by
  unfold plus empty
  obtain ⟨h, hm, hheq⟩ := heapMerge_empty_right a.heap
  simp only [hm, maskPlus_empty_right, hheq, dif_pos a.wf]

/-- `stabilize (core φ) = empty` for every φ. -/
theorem stabilize_core_eq_empty (φ : VirtualState) : stabilize (core φ) = empty := by
  apply VirtualState.ext
  · simp [VirtualState.empty]
  · refine Std.ExtTreeMap.ext_getElem? ?_
    intro hl
    change (stabilize (core φ)).heap.get? hl = empty.heap.get? hl
    rw [stabilize_heap_get?]
    simp [core_mask, VirtualState.empty, Std.ExtTreeMap.getD_empty, preal.ppos]

/-- Every state decomposes as `stabilize φ ⊕ core φ`. -/
theorem decompose_stabilize_pure (φ : VirtualState) :
    plus (stabilize φ) (core φ) = some φ := by
  have hcomp : heapCompatible (stabilize φ).heap (core φ).heap := by
    rw [heapCompatible_iff_forall]
    intro hl v₁ v₂ h1 h2
    have h2' : φ.heap.get? hl = some v₂ := by simpa [core_heap] using h2
    rw [stabilize_heap_get?] at h1
    by_cases hp : (φ.mask.getD hl 0).ppos
    · simp [hp] at h1
      have h1' : φ.heap.get? hl = some v₁ := by simpa using h1
      rw [h1'] at h2'
      exact Option.some.inj h2'
    · simp [hp] at h1
  have hunion : (stabilize φ).heap ∪ (core φ).heap = φ.heap := by
    refine Std.ExtTreeMap.ext_getElem? ?_
    intro hl
    cases hs : (stabilize φ).heap.get? hl with
    | none =>
      have hnotmem : ¬ hl ∈ (stabilize φ).heap := by
        intro hmem
        have : (stabilize φ).heap.get? hl = some ((stabilize φ).heap.get hl hmem) :=
          Std.ExtTreeMap.getElem?_eq_some_getElem hmem
        rw [hs] at this
        simp at this
      simpa [core_heap] using
        (Std.ExtTreeMap.getElem?_union_of_not_mem_left
          (t₁ := (stabilize φ).heap) (t₂ := (core φ).heap) hnotmem)
    | some v =>
      have hφ : φ.heap.get? hl = some v := by
        rw [stabilize_heap_get?] at hs
        by_cases hp : (φ.mask.getD hl 0).ppos
        · simpa [hp] using hs
        · simp [hp] at hs
      have hs' : (stabilize φ).heap.get? hl = some v := by simpa using hs
      have hφ' : (core φ).heap.get? hl = some v := by simpa [core_heap] using hφ
      have hu := Std.ExtTreeMap.getElem?_union
        (t₁ := (stabilize φ).heap) (t₂ := (core φ).heap) (k := hl)
      have hs'' : (stabilize φ).heap[hl]? = some v := by simpa using hs'
      have hφ'' : (core φ).heap[hl]? = some v := by simpa using hφ'
      rw [hs'', hφ''] at hu
      have hφ''' : φ.heap[hl]? = some v := by simpa using hφ
      simpa [hφ'''] using hu
  have hmerge : heapMerge (stabilize φ).heap (core φ).heap = some φ.heap := by
    have hcomp' : heapCompatible (stabilize φ).heap φ.heap := by
      simpa [core_heap] using hcomp
    have hunion' : (stabilize φ).heap ∪ φ.heap = φ.heap := by
      simpa [core_heap] using hunion
    unfold heapMerge
    simp [hcomp', hunion']
  unfold plus
  rw [hmerge, core_mask, stabilize_mask, maskPlus_empty_right]
  simp [φ.wf]

theorem stabilize_core_emp {a b c : VirtualState}
    (h : plus b (stabilize (core c)) = some a) : a = b := by
  rw [stabilize_core_eq_empty, plus_empty_right] at h
  exact (Option.some.inj h).symm

theorem stabilize_core_emp_left {a b c : VirtualState}
    (h : plus (stabilize (core c)) b = some a) : a = b := by
  rw [stabilize_core_eq_empty, plus_empty_left] at h
  exact (Option.some.inj h).symm

/-- `Disjoint` is symmetric. -/
theorem Disjoint.symm {a b : VirtualState} (h : Disjoint a b) : Disjoint b a := by
  rcases Option.isSome_iff_exists.mp (by simpa [Disjoint] using h) with ⟨x, hx⟩
  exact disjoint_of_plus (plus_comm hx)

/-- `stabilize` distributes over `plus`. -/
theorem stabilize_sum {a b x : VirtualState} (h : plus a b = some x) :
    plus (stabilize a) (stabilize b) = some (stabilize x) := by
  have hcomp : heapCompatible (stabilize a).heap (stabilize b).heap := by
    rw [heapCompatible_iff_forall]
    intro hl v₁ v₂ ha hb
    have ha' : a.heap.get? hl = some v₁ := by
      rw [stabilize_heap_get?] at ha
      by_cases hpa : (a.mask.getD hl 0).ppos
      · simpa [hpa] using ha
      · simp [hpa] at ha
    have hb' : b.heap.get? hl = some v₂ := by
      rw [stabilize_heap_get?] at hb
      by_cases hpb : (b.mask.getD hl 0).ppos
      · simpa [hpb] using hb
      · simp [hpb] at hb
    have hx1 : x.heap.get? hl = some v₁ := plus_heap_of_left h ha'
    have hx2 : x.heap.get? hl = some v₂ := plus_heap_of_right h hb'
    rw [hx1] at hx2
    exact Option.some.inj hx2
  have hunion : (stabilize a).heap ∪ (stabilize b).heap = (stabilize x).heap := by
    refine Std.ExtTreeMap.ext_getElem? ?_
    intro hl
    by_cases hpa : (a.mask.getD hl 0).ppos <;> by_cases hpb : (b.mask.getD hl 0).ppos
    · have hax : (a.heap.get? hl).isSome := heap_isSome_of_ppos hpa
      have hbx : (b.heap.get? hl).isSome := heap_isSome_of_ppos hpb
      cases ha : a.heap.get? hl with
      | none =>
        exfalso
        have hmem : hl ∈ a.heap := (Std.ExtTreeMap.mem_iff_isSome_getElem?).mpr hax
        have his : a.heap.get? hl = some (a.heap.get hl hmem) :=
          Std.ExtTreeMap.getElem?_eq_some_getElem hmem
        rw [ha] at his
        simp at his
      | some va =>
        cases hb : b.heap.get? hl with
        | none =>
          exfalso
          have hmem : hl ∈ b.heap := (Std.ExtTreeMap.mem_iff_isSome_getElem?).mpr hbx
          have his : b.heap.get? hl = some (b.heap.get hl hmem) :=
            Std.ExtTreeMap.getElem?_eq_some_getElem hmem
          rw [hb] at his
          simp at his
        | some vb =>
          have hva : x.heap.get? hl = some va := plus_heap_of_left h ha
          have hvb : x.heap.get? hl = some vb := plus_heap_of_right h hb
          have hv : va = vb := by rw [hva] at hvb; exact Option.some.inj hvb
          have hsum : (x.mask.getD hl 0).ppos := by
            rw [plus_mask_eq h, maskPlus_getD]
            exact preal.ppos_add_of_left hpa
          have hsa0 : (stabilize a).heap.get? hl = some va := by
            rw [stabilize_heap_get?]
            simpa [hpa] using ha
          have hsb0 : (stabilize b).heap.get? hl = some vb := by
            rw [stabilize_heap_get?]
            simpa [hpb] using hb
          have hsa : (stabilize a).heap[hl]? = some va := by simpa using hsa0
          have hsb : (stabilize b).heap[hl]? = some vb := by simpa using hsb0
          have hu := Std.ExtTreeMap.getElem?_union
            (t₁ := (stabilize a).heap) (t₂ := (stabilize b).heap) (k := hl)
          rw [hsa, hsb] at hu
          have hu' : ((stabilize a).heap ∪ (stabilize b).heap)[hl]? = some va := by
            simpa [hv] using hu
          have hsx0 : (stabilize x).heap.get? hl = some va := by
            rw [stabilize_heap_get?]
            simpa [hsum] using hva
          have hsx : (stabilize x).heap[hl]? = some va := by simpa using hsx0
          exact hu'.trans hsx.symm
    · have hax : (a.heap.get? hl).isSome := heap_isSome_of_ppos hpa
      cases ha : a.heap.get? hl with
      | none =>
        exfalso
        have hmem : hl ∈ a.heap := (Std.ExtTreeMap.mem_iff_isSome_getElem?).mpr hax
        have his : a.heap.get? hl = some (a.heap.get hl hmem) :=
          Std.ExtTreeMap.getElem?_eq_some_getElem hmem
        rw [ha] at his
        simp at his
      | some va =>
        have hsum : (x.mask.getD hl 0).ppos := by
          rw [plus_mask_eq h, maskPlus_getD]
          exact preal.ppos_add_of_left hpa
        have hsa0 : (stabilize a).heap.get? hl = some va := by
          rw [stabilize_heap_get?]
          simpa [hpa] using ha
        have hsb0 : (stabilize b).heap.get? hl = none := by
          rw [stabilize_heap_get?]
          simp [hpb]
        have hsa : (stabilize a).heap[hl]? = some va := by simpa using hsa0
        have hsb : (stabilize b).heap[hl]? = none := by simpa using hsb0
        have hnotmem : ¬ hl ∈ (stabilize b).heap := by
          intro hmem
          have his : (stabilize b).heap.get? hl = some ((stabilize b).heap.get hl hmem) :=
            Std.ExtTreeMap.getElem?_eq_some_getElem hmem
          rw [hsb0] at his
          simp at his
        have hu := Std.ExtTreeMap.getElem?_union_of_not_mem_right
          (t₁ := (stabilize a).heap) (t₂ := (stabilize b).heap) hnotmem
        have hva : x.heap.get? hl = some va := plus_heap_of_left h ha
        have hsx0 : (stabilize x).heap.get? hl = some va := by
          rw [stabilize_heap_get?]
          simpa [hsum] using hva
        have hsx : (stabilize x).heap[hl]? = some va := by simpa using hsx0
        rw [hsa] at hu
        exact hu.trans hsx.symm
    · have hbx : (b.heap.get? hl).isSome := heap_isSome_of_ppos hpb
      cases hb : b.heap.get? hl with
      | none =>
        exfalso
        have hmem : hl ∈ b.heap := (Std.ExtTreeMap.mem_iff_isSome_getElem?).mpr hbx
        have his : b.heap.get? hl = some (b.heap.get hl hmem) :=
          Std.ExtTreeMap.getElem?_eq_some_getElem hmem
        rw [hb] at his
        simp at his
      | some vb =>
        have hsum : (x.mask.getD hl 0).ppos := by
          rw [plus_mask_eq h, maskPlus_getD]
          exact preal.ppos_add_of_right hpb
        have hsa0 : (stabilize a).heap.get? hl = none := by
          rw [stabilize_heap_get?]
          simp [hpa]
        have hsb0 : (stabilize b).heap.get? hl = some vb := by
          rw [stabilize_heap_get?]
          simpa [hpb] using hb
        have hsa : (stabilize a).heap[hl]? = none := by simpa using hsa0
        have hsb : (stabilize b).heap[hl]? = some vb := by simpa using hsb0
        have hnotmem : ¬ hl ∈ (stabilize a).heap := by
          intro hmem
          have his : (stabilize a).heap.get? hl = some ((stabilize a).heap.get hl hmem) :=
            Std.ExtTreeMap.getElem?_eq_some_getElem hmem
          rw [hsa0] at his
          simp at his
        have hu := Std.ExtTreeMap.getElem?_union_of_not_mem_left
          (t₁ := (stabilize a).heap) (t₂ := (stabilize b).heap) hnotmem
        have hvb : x.heap.get? hl = some vb := plus_heap_of_right h hb
        have hsx0 : (stabilize x).heap.get? hl = some vb := by
          rw [stabilize_heap_get?]
          simpa [hsum] using hvb
        have hsx : (stabilize x).heap[hl]? = some vb := by simpa using hsx0
        rw [hsb] at hu
        exact hu.trans hsx.symm
    · have hsa0 : (stabilize a).heap.get? hl = none := by
        rw [stabilize_heap_get?]
        simp [hpa]
      have hsb0 : (stabilize b).heap.get? hl = none := by
        rw [stabilize_heap_get?]
        simp [hpb]
      have hsa : (stabilize a).heap[hl]? = none := by simpa using hsa0
      have hsb : (stabilize b).heap[hl]? = none := by simpa using hsb0
      have hnotmem : ¬ hl ∈ (stabilize a).heap := by
        intro hmem
        have his : (stabilize a).heap.get? hl = some ((stabilize a).heap.get hl hmem) :=
          Std.ExtTreeMap.getElem?_eq_some_getElem hmem
        rw [hsa0] at his
        simp at his
      have hu := Std.ExtTreeMap.getElem?_union_of_not_mem_left
        (t₁ := (stabilize a).heap) (t₂ := (stabilize b).heap) hnotmem
      have hsum : ¬ (x.mask.getD hl 0).ppos := by
        rw [plus_mask_eq h, maskPlus_getD]
        exact preal.not_ppos_add hpa hpb
      have hsx0 : (stabilize x).heap.get? hl = none := by
        rw [stabilize_heap_get?]
        simp [hsum]
      have hsx : (stabilize x).heap[hl]? = none := by simpa using hsx0
      rw [hsb] at hu
      exact hu.trans hsx.symm
  have hmerge : heapMerge (stabilize a).heap (stabilize b).heap = some (stabilize x).heap := by
    unfold heapMerge
    simpa [hcomp, hunion]
  have hmask : maskPlus (stabilize a).mask (stabilize b).mask = (stabilize x).mask := by
    calc
      maskPlus (stabilize a).mask (stabilize b).mask = maskPlus a.mask b.mask := by rfl
      _ = x.mask := (plus_mask_eq h).symm
      _ = (stabilize x).mask := by rfl
  have hwf : wfPreVirtualState (maskPlus (stabilize a).mask (stabilize b).mask) (stabilize x).heap := by
    rw [hmask]
    exact (stabilize x).wf
  unfold plus
  rw [hmerge]
  dsimp
  split
  · rename_i hWF
    apply congrArg some
    exact VirtualState.ext hmask rfl
  · rename_i hWF
    exact False.elim (hWF hwf)

/-- `plus` is associative in the exists sense. -/
theorem plus_assoc_exists
    {a b c ab x : VirtualState}
    (hab : plus a b = some ab) (hxc : plus ab c = some x) :
    ∃ bc, plus b c = some bc ∧ plus a bc = some x := by
  have hcomp_ab : heapCompatible a.heap b.heap := by
    exact heapMerge_isSome_iff.mp (Option.isSome_of_eq_some (plus_heapMerge_eq hab))
  have hcomp_xc : heapCompatible ab.heap c.heap := by
    exact heapMerge_isSome_iff.mp (Option.isSome_of_eq_some (plus_heapMerge_eq hxc))
  have hcomp_bc : heapCompatible b.heap c.heap := by
    rw [heapCompatible_iff_forall]
    intro hl vb vc hb hc
    have hab_vb : ab.heap.get? hl = some vb := plus_heap_of_right hab hb
    exact (heapCompatible_iff_forall.mp hcomp_xc) hl vb vc hab_vb hc
  have hcomp_ac : heapCompatible a.heap c.heap := by
    rw [heapCompatible_iff_forall]
    intro hl va vc ha hc
    have hab_va : ab.heap.get? hl = some va := plus_heap_of_left hab ha
    exact (heapCompatible_iff_forall.mp hcomp_xc) hl va vc hab_va hc
  have hmask_xbc : maskPlus a.mask (maskPlus b.mask c.mask) = x.mask := by
    calc
      maskPlus a.mask (maskPlus b.mask c.mask)
        = maskPlus (maskPlus a.mask b.mask) c.mask := (maskPlus_assoc a.mask b.mask c.mask).symm
      _ = maskPlus ab.mask c.mask := by rw [← plus_mask_eq hab]
      _ = x.mask := (plus_mask_eq hxc).symm
  have hm_bc : heapMerge b.heap c.heap = some (b.heap ∪ c.heap) := by
    unfold heapMerge
    simp [hcomp_bc]
  have hwf_bc : wfPreVirtualState (maskPlus b.mask c.mask) (b.heap ∪ c.heap) := by
    constructor
    · unfold wfHeapDom
      rw [List.all_eq_true]
      intro hl hkey
      have hmem : hl ∈ maskPlus b.mask c.mask := (Std.ExtTreeMap.mem_keys).mp hkey
      have hcont : (maskPlus b.mask c.mask).contains hl = true :=
        (Std.ExtTreeMap.mem_iff_contains).1 hmem
      have hget :
          (maskPlus b.mask c.mask).get? hl =
            some ((maskPlus b.mask c.mask).getD hl 0) :=
        Std.ExtTreeMap.getElem?_eq_some_getD_of_contains
          (t := maskPlus b.mask c.mask) (a := hl) (fallback := 0) hcont
      rw [hget]
      simp
      by_cases hp : ((maskPlus b.mask c.mask).getD hl 0).ppos
      · right
        by_cases hbp : (b.mask.getD hl 0).ppos
        · left
          exact (Std.ExtTreeMap.mem_iff_isSome_getElem?).2 (heap_isSome_of_ppos (φ := b) hbp)
        · right
          have hcp : (c.mask.getD hl 0).ppos := by
            rw [maskPlus_getD, preal.eq_zero_of_not_ppos hbp, preal.zero_add] at hp
            exact hp
          exact (Std.ExtTreeMap.mem_iff_isSome_getElem?).2 (heap_isSome_of_ppos (φ := c) hcp)
      · exact Or.inl hp
    · unfold wfMaskSimple
      rw [List.all_eq_true]
      intro hl hkey
      have hmem : hl ∈ maskPlus b.mask c.mask := (Std.ExtTreeMap.mem_keys).mp hkey
      have hcont : (maskPlus b.mask c.mask).contains hl = true :=
        (Std.ExtTreeMap.mem_iff_contains).1 hmem
      have hget :
          (maskPlus b.mask c.mask).get? hl =
            some ((maskPlus b.mask c.mask).getD hl 0) :=
        Std.ExtTreeMap.getElem?_eq_some_getD_of_contains
          (t := maskPlus b.mask c.mask) (a := hl) (fallback := 0) hcont
      have hxcont : x.mask.contains hl = true := by
        rw [← hmask_xbc, maskPlus_contains]
        simp [hcont]
      have hxmem : hl ∈ x.mask := (Std.ExtTreeMap.mem_iff_contains).2 hxcont
      have hxkey : hl ∈ x.mask.keys := (Std.ExtTreeMap.mem_keys).2 hxmem
      have hxget : x.mask.get? hl = some (x.mask.getD hl 0) :=
        Std.ExtTreeMap.getElem?_eq_some_getD_of_contains
          (t := x.mask) (a := hl) (fallback := 0) hxcont
      have hboundx := (List.all_eq_true.mp x.wf.2) hl hxkey
      rw [hxget] at hboundx
      simp at hboundx
      have hle : ((maskPlus b.mask c.mask).getD hl 0).val ≤ (x.mask.getD hl 0).val := by
        rw [maskPlus_getD b.mask c.mask hl, ← hmask_xbc, maskPlus_getD a.mask (maskPlus b.mask c.mask) hl,
          maskPlus_getD b.mask c.mask hl]
        change (b.mask.getD hl 0 + c.mask.getD hl 0).val ≤
          (a.mask.getD hl 0 + (b.mask.getD hl 0 + c.mask.getD hl 0)).val
        simp [preal.add_val]
        have ha_nonneg : 0 ≤ (a.mask.getD hl 0).val := (a.mask.getD hl 0).nonneg
        grind
      rw [hget]
      simp
      change ((maskPlus b.mask c.mask).getD hl 0).val ≤ 1
      exact le_trans hle hboundx
  let bc : VirtualState :=
    { mask := maskPlus b.mask c.mask
      heap := b.heap ∪ c.heap
      wf := hwf_bc }
  have hbc : plus b c = some bc := by
    unfold plus
    dsimp [bc]
    rw [hm_bc]
    dsimp
    split
    · rename_i hWF
      apply congrArg some
      exact VirtualState.ext rfl rfl
    · rename_i hWF
      exact False.elim (hWF hwf_bc)
  have hcomp_abc : heapCompatible a.heap bc.heap := by
    rw [heapCompatible_iff_forall]
    intro hl va vbc ha hbcv
    dsimp [bc] at hbcv ⊢
    cases hb : b.heap.get? hl with
    | none =>
      have hnotmem : ¬ hl ∈ b.heap := by
        intro hmem
        have his : b.heap.get? hl = some (b.heap.get hl hmem) :=
          Std.ExtTreeMap.getElem?_eq_some_getElem hmem
        rw [hb] at his
        simp at his
      have hc : c.heap.get? hl = some vbc := by
        have hu := Std.ExtTreeMap.getElem?_union_of_not_mem_left
          (t₁ := b.heap) (t₂ := c.heap) hnotmem
        rw [hbcv] at hu
        simpa using hu.symm
      have hab_va : ab.heap.get? hl = some va := plus_heap_of_left hab ha
      exact (heapCompatible_iff_forall.mp hcomp_xc) hl va vbc hab_va hc
    | some vb =>
      have hva_vb : va = vb := (heapCompatible_iff_forall.mp hcomp_ab) hl va vb ha hb
      have hub : (b.heap ∪ c.heap).get? hl = some vb := heapMerge_get?_of_left hm_bc hb
      have hub' : (b.heap ∪ c.heap)[hl]? = some vb := by simpa using hub
      rw [hub'] at hbcv
      exact hva_vb.trans (Option.some.inj hbcv)
  have habHeap : ab.heap = a.heap ∪ b.heap := by
    have hm := plus_heapMerge_eq hab
    have hm' : some (a.heap ∪ b.heap) = some ab.heap := by
      simpa [heapMerge, hcomp_ab] using hm
    exact Option.some.inj hm'.symm
  have hxcHeap : x.heap = ab.heap ∪ c.heap := by
    have hm := plus_heapMerge_eq hxc
    have hm' : some (ab.heap ∪ c.heap) = some x.heap := by
      simpa [heapMerge, hcomp_xc] using hm
    exact Option.some.inj hm'.symm
  have hunion_ax : a.heap ∪ bc.heap = x.heap := by
    dsimp [bc]
    calc
      a.heap ∪ (b.heap ∪ c.heap) = (a.heap ∪ b.heap) ∪ c.heap := by
        rw [heapUnion_assoc]
      _ = ab.heap ∪ c.heap := by rw [habHeap]
      _ = x.heap := by rw [hxcHeap]
  have hmerge_ax : heapMerge a.heap bc.heap = some x.heap := by
    dsimp [bc]
    have hcomp_abc' : heapCompatible a.heap (b.heap ∪ c.heap) := by
      simpa [bc] using hcomp_abc
    unfold heapMerge
    simpa [hcomp_abc', hunion_ax]
  have hwf_ax : wfPreVirtualState (maskPlus a.mask bc.mask) x.heap := by
    dsimp [bc]
    rw [hmask_xbc]
    exact x.wf
  have hax : plus a bc = some x := by
    unfold plus
    dsimp [bc]
    rw [hmerge_ax]
    dsimp
    split
    · rename_i hWF
      apply congrArg some
      exact VirtualState.ext hmask_xbc rfl
    · rename_i hWF
      exact False.elim (hWF hwf_ax)
  exact ⟨bc, hbc, hax⟩

end VirtualState

-- ============================================================================
-- § Assertions and sep logic (§§ 5–8 of IDF_basic)
-- ============================================================================

abbrev Assertion := VirtualState → Prop

namespace Assertion

def entails (P Q : Assertion) : Prop := ∀ φ, P φ → Q φ
infix:55 " ⊢ " => entails

def sep (P Q : Assertion) : Assertion :=
  fun φ => ∃ φ₁ φ₂, VirtualState.plus φ₁ φ₂ = some φ ∧ P φ₁ ∧ Q φ₂
infixr:70 " ∗ " => sep

/-- `emp`: the image of `stabilize ∘ core`, Isabelle-style. -/
def emp : Assertion :=
  fun φ => ∃ b : VirtualState, φ = VirtualState.stabilize (VirtualState.core b)

theorem emp_iff_empty (φ : VirtualState) : emp φ ↔ φ = VirtualState.empty := by
  constructor
  · rintro ⟨b, hb⟩; rw [hb]; exact VirtualState.stabilize_core_eq_empty b
  · intro heq
    exact ⟨VirtualState.empty, by rw [heq]; exact (VirtualState.stabilize_core_eq_empty _).symm⟩

def SelfFraming (P : Assertion) : Prop := ∀ φ, P φ ↔ P (VirtualState.stabilize φ)
def Stabilize (A : Assertion) : Assertion := fun φ => A (VirtualState.stabilize φ)
def semp : Assertion := Stabilize emp
def StableAssert (A : Assertion) : Prop := A ⊢ Stabilize A

theorem Stabilize_selfFraming (A : Assertion) : SelfFraming (Stabilize A) := by
  intro φ; unfold Stabilize; constructor <;> intro h <;>
    simpa [VirtualState.stable_eq_stabilize (VirtualState.stabilize_stable φ)] using h

theorem selfFraming_ext {A B : Assertion}
    (hA : SelfFraming A) (hB : SelfFraming B)
    (hAB : ∀ φ, VirtualState.Stable φ → A φ → B φ)
    (hBA : ∀ φ, VirtualState.Stable φ → B φ → A φ) : A = B := by
  funext φ; apply propext; constructor
  · intro hφ
    exact (hB φ).mpr (hAB _ (VirtualState.stabilize_stable φ) ((hA φ).mp hφ))
  · intro hφ
    exact (hA φ).mpr (hBA _ (VirtualState.stabilize_stable φ) ((hB φ).mp hφ))

theorem selfFraming_iff_eq_stabilize (A : Assertion) : SelfFraming A ↔ A = Stabilize A := by
  constructor
  · intro hA
    apply selfFraming_ext hA (Stabilize_selfFraming A)
    · intro φ hs hφ; simpa [Stabilize, VirtualState.stable_eq_stabilize hs] using hφ
    · intro φ hs hφ; simpa [Stabilize, VirtualState.stable_eq_stabilize hs] using hφ
  · intro hEq; rw [hEq]; exact Stabilize_selfFraming A

theorem selfFraming_semp : SelfFraming semp := by
  unfold semp; exact Stabilize_selfFraming emp

theorem semp_iff_stabilize_empty (φ : VirtualState) :
    semp φ ↔ VirtualState.stabilize φ = VirtualState.empty := by
  unfold semp Stabilize; rw [emp_iff_empty]

theorem StableAssert_emp : StableAssert emp := by
  intro φ hφ
  unfold Stabilize emp at *
  obtain ⟨b, hb⟩ := hφ
  refine ⟨b, ?_⟩
  rw [hb]
  exact VirtualState.stable_eq_stabilize (VirtualState.stabilize_stable _)

theorem StableAssert_semp : StableAssert semp := by
  intro φ hφ
  unfold semp Stabilize at hφ ⊢
  simpa [VirtualState.stable_eq_stabilize (VirtualState.stabilize_stable φ)] using hφ

theorem entails_star_semp (A : Assertion) : A ⊢ A ∗ semp := by
  intro φ hA
  refine ⟨φ, VirtualState.empty, VirtualState.plus_empty_right φ, hA, ?_⟩
  rw [semp_iff_stabilize_empty]
  have hempty : VirtualState.empty.Stable := by
    rw [VirtualState.stable_iff_forall]
    intro hl v hget
    simp [VirtualState.empty] at hget
  simpa using VirtualState.stable_eq_stabilize hempty

theorem star_semp_entails_of_selfFraming (A : Assertion) (hA : SelfFraming A) :
    A ∗ semp ⊢ A := by
  intro φ hφ
  rcases hφ with ⟨φ₁, φ₂, hplus, hφ₁A, hφ₂semp⟩
  have hφ₁st : A (VirtualState.stabilize φ₁) := (hA φ₁).mp hφ₁A
  have hφ₂empty : VirtualState.stabilize φ₂ = VirtualState.empty :=
    (semp_iff_stabilize_empty φ₂).mp hφ₂semp
  have hsum := VirtualState.stabilize_sum hplus
  rw [hφ₂empty, VirtualState.plus_empty_right] at hsum
  have hEq : VirtualState.stabilize φ₁ = VirtualState.stabilize φ := Option.some.inj hsum
  exact (hA φ).mpr (hEq ▸ hφ₁st)

-- ============================================================================
-- § Identity laws
-- ============================================================================

theorem sep_emp_entails (A : Assertion) : A ∗ emp ⊢ A := by
  intro φ ⟨φ₁, φ₂, hplus, hA, ⟨b, hb⟩⟩
  rw [hb] at hplus
  exact (VirtualState.stabilize_core_emp hplus) ▸ hA

theorem entails_sep_emp (A : Assertion) : A ⊢ A ∗ emp := by
  intro φ hA
  exact ⟨φ, VirtualState.empty, VirtualState.plus_empty_right φ, hA,
    ⟨VirtualState.empty, (VirtualState.stabilize_core_eq_empty _).symm⟩⟩

theorem emp_sep_entails (A : Assertion) : emp ∗ A ⊢ A := by
  intro φ ⟨φ₁, φ₂, hplus, ⟨b, hb⟩, hA⟩
  rw [hb] at hplus
  exact (VirtualState.stabilize_core_emp_left hplus) ▸ hA

theorem entails_emp_sep (A : Assertion) : A ⊢ emp ∗ A := by
  intro φ hA
  exact ⟨VirtualState.empty, φ, VirtualState.plus_empty_left φ,
    ⟨VirtualState.empty, (VirtualState.stabilize_core_eq_empty _).symm⟩, hA⟩

-- ============================================================================
-- § Stable_emp
-- ============================================================================

theorem Stable_emp : ∀ φ, emp φ → emp (VirtualState.stabilize φ) := by
  intro φ hemp
  rw [emp_iff_empty] at hemp ⊢
  rw [hemp]
  have hempty : VirtualState.empty.Stable := by
    rw [VirtualState.stable_iff_forall]
    intro hl v hget
    simp [VirtualState.empty] at hget
  simpa using VirtualState.stable_eq_stabilize hempty

theorem SelfFraming_emp_on_stable :
    ∀ φ, VirtualState.Stable φ → (emp φ ↔ emp (VirtualState.stabilize φ)) := by
  intro φ hs; rw [VirtualState.stable_eq_stabilize hs]

-- ============================================================================
-- § Points-to assertions
-- ============================================================================

def acc (hl : HeapLoc) (p : preal) : Assertion :=
  fun φ => p.ppos ∧ p ≤ φ.getPerm hl

def fieldEq (hl : HeapLoc) (v : Val) : Assertion :=
  fun φ => φ.heap.get? hl = some v

def pointsToDirect (hl : HeapLoc) (p : preal) (v : Val) : Assertion :=
  fun φ => p.ppos ∧ p ≤ φ.getPerm hl ∧ φ.heap.get? hl = some v

def pointsToFrac (hl : HeapLoc) (p : preal) (v : Val) : Assertion :=
  acc hl p ∗ fieldEq hl v

def pointsTo (hl : HeapLoc) (v : Val) : Assertion := pointsToDirect hl 1 v

theorem selfFraming_acc (hl : HeapLoc) (p : preal) : SelfFraming (acc hl p) := by
  intro φ; simp [acc, VirtualState.getPerm, VirtualState.stabilize_mask]

theorem selfFraming_pointsToDirect (hl : HeapLoc) (p : preal) (v : Val) :
    SelfFraming (pointsToDirect hl p v) := by
  intro φ
  simp only [pointsToDirect, VirtualState.getPerm, VirtualState.stabilize_mask]
  constructor
  · rintro ⟨hp, hle, hheap⟩
    have hppos : (φ.mask.getD hl 0).ppos := by
      unfold preal.ppos at hp ⊢
      unfold LE.le preal.instLE at hle
      exact lt_of_lt_of_le hp hle
    refine ⟨hp, hle, ?_⟩
    rw [VirtualState.stabilize_heap_get?, if_pos hppos]; exact hheap
  · rintro ⟨hp, hle, hheap⟩
    refine ⟨hp, hle, ?_⟩
    rw [VirtualState.stabilize_heap_get?] at hheap
    have hppos : (φ.mask.getD hl 0).ppos := by
      unfold preal.ppos at hp ⊢
      unfold LE.le preal.instLE at hle
      exact lt_of_lt_of_le hp hle
    simp only [hppos, if_true] at hheap; exact hheap

theorem pointsToDirect_entails_acc (hl : HeapLoc) (p : preal) (v : Val) :
    pointsToDirect hl p v ⊢ acc hl p := fun _ h => ⟨h.1, h.2.1⟩

theorem pointsToDirect_entails_fieldEq (hl : HeapLoc) (p : preal) (v : Val) :
    pointsToDirect hl p v ⊢ fieldEq hl v := fun _ h => h.2.2

end Assertion

-- ============================================================================
-- § Examples
-- ============================================================================

namespace Examples

open Assertion

def pf (pAddr : Address) : HeapLoc := ⟨pAddr, "f"⟩

def ex1 (pAddr : Address) : Assertion := pointsToDirect (pf pAddr) 1 (Val.vInt 5)
def ex1_sep (pAddr : Address) : Assertion := acc (pf pAddr) 1 ∗ fieldEq (pf pAddr) (Val.vInt 5)

theorem ex1_selfFraming (pAddr : Address) : SelfFraming (ex1 pAddr) := by
  simpa [ex1] using selfFraming_pointsToDirect (pf pAddr) 1 (Val.vInt 5)

end Examples

end IDFExecutable
