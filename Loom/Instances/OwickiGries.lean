import Loom.Instances.SepLogFracWithoutAxiom

open Lean.Order Loom


structure Counter where
  cval : Loc
  ct1  : Loc
  ct2  : Loc

structure Counter.WF (c : Counter) : Prop where
  val_ne_t1 : c.cval ≠ c.ct1
  val_ne_t2 : c.cval ≠ c.ct2
  t1_ne_t2  : c.ct1  ≠ c.ct2


def guard_INV (c : Counter) (vv v1 v2 : Val) : hProp :=
  (((c.cval ↦ vv)
  ∗ (c.ct1 ↦[halfPerm] v1)) ∗ ⌜vv = v1 + v2⌝ʰ)
  ∗ (c.ct2 ↦[halfPerm] v2)

def guard_INV_ex (c : Counter) : hProp :=
  ∃ʰ vv, ∃ʰ v1, ∃ʰ v2, guard_INV c vv v1 v2

theorem guard_INV_ex_intro (c : Counter) (vv v1 v2 : Val) :
    guard_INV c vv v1 v2 ⊑ guard_INV_ex c :=
  fun h hh => hExists'.intro vv (hExists'.intro v1 (hExists'.intro v2 hh))


def inc_PRE (c : Counter) (tid : Bool) (old_ti : Val) : hProp :=
  if tid = false
  then c.ct1 ↦[halfPerm] old_ti
  else c.ct2 ↦[halfPerm] old_ti

def inc_POST (c : Counter) (tid : Bool) (old_ti : Val) : hProp :=
  if tid = false
  then c.ct1 ↦[halfPerm] (old_ti + 1)
  else c.ct2 ↦[halfPerm] (old_ti + 1)

private theorem half_add_half_le : halfPerm.1 + halfPerm.1 ≤ 1 := by
  simp [halfPerm]; change (1/2 : Rat) + 1/2 ≤ 1; grind

private theorem half_add_half_eq_full :
    (⟨halfPerm.1 + halfPerm.1, half_add_half_le⟩ : { p : Perm // ValidPerm p }) = fullPermVal := by
  simp [halfPerm, fullPermVal]; ext; simp; change (1/2 : Rat) + 1/2 = 1; grind

theorem half_half_is_full (x : Loc) (v : Val) :
    (x ↦[halfPerm] v) ∗ (x ↦[halfPerm] v) = (x ↦ v) := by
  rw [hSingleFrac_combine x v halfPerm halfPerm half_add_half_le,
      half_add_half_eq_full, ← hSingle_eq_hSingleFrac]

theorem full_is_half_half (x : Loc) (v : Val) :
    (x ↦ v) = (x ↦[halfPerm] v) ∗ (x ↦[halfPerm] v) :=
  (half_half_is_full x v).symm


theorem HeapM.consequence {pre pre' : hProp} {post post' : α → hProp} (x : HeapM α)
    (hpre  : pre ⊑ pre')
    (hpost : ∀ a, post' a ⊑ post a)
    (hx    : ⦃ pre' ⦄ x ⦃ post' ⦄) :
    ⦃ pre ⦄ x ⦃ post ⦄ := by
  apply Triple.iff.mpr
  have hwp := Triple.iff.mp hx
  unfold wp wpTrans at *
  simp_all [instWPMonadHeapMHPropNil]
  apply hForall_intro; intro H
  apply entails_hWand
  intro heap HH
  apply x.monotone
  · rfl
  · intro a; exact hStar_mono (hpost a)
  · apply hForall_star_elim H (P := fun H' => H' -∗ x.predTrans (fun a => H' ∗ post' a) epost⟨⟩)
    apply hWand_elim
    apply hStar_mono
    assumption
    revert HH heap
    apply hStar_mono
    apply hpre



def inc_t0 (c : Counter) : HeapM Unit := do
  HeapM.inhale (guard_INV_ex c)
  let vv ← HeapM.read c.cval
  HeapM.assign c.cval (vv + 1)
  let v1 ← HeapM.read c.ct1
  HeapM.assign c.ct1 (v1 + 1)
  HeapM.exhale (guard_INV_ex c)

def inc_t1 (c : Counter) : HeapM Unit := do
  HeapM.inhale (guard_INV_ex c)
  let vv ← HeapM.read c.cval
  HeapM.assign c.cval (vv + 1)
  let v2 ← HeapM.read c.ct2
  HeapM.assign c.ct2 (v2 + 1)
  HeapM.exhale (guard_INV_ex c)

/-! guard_INV rearranged to put ct1 or ct2 first -/

private theorem guard_INV_rearrange_ct1 (c : Counter) (vv v1 v2 : Val) :
    guard_INV c vv v1 v2 =
    (c.ct1 ↦[halfPerm] v1) ∗ (((c.cval ↦ vv) ∗ ⌜vv = v1 + v2⌝ʰ) ∗ (c.ct2 ↦[halfPerm] v2)) := by
  unfold guard_INV
  rw [hStar_comm (c.cval ↦ vv) (c.ct1 ↦[halfPerm] v1), hStar_assoc, hStar_assoc]
  simp
  ext
  constructor
  rename_i heap
  revert heap
  apply hStar_mono
  simp[←hStar_comm, ←hStar_assoc]
  rfl
  rename_i heap
  revert heap
  apply hStar_mono
  simp[←hStar_comm, ←hStar_assoc]
  rfl

theorem guard_INV_pins_v1 (c : Counter) (vv v1 v2 ot1 : Val)
    {P : hProp} {h : Heap}
    (hINV : guard_INV c vv v1 v2 h)
    (hPre : (P ∗ (c.ct1 ↦[halfPerm] ot1)) h) :
    v1 = ot1 := by
  rw [guard_INV_rearrange_ct1] at hINV
  exact hStar_singleFrac_unique hINV (hStar_comm_entails h hPre)

theorem guard_INV_pins_v2 (c : Counter) (vv v1 v2 ot2 : Val)
    {P : hProp} {h : Heap}
    (hINV : guard_INV c vv v1 v2 h)
    (hPre : (P ∗ (c.ct2 ↦[halfPerm] ot2)) h) :
    v2 = ot2 := by
  unfold guard_INV at hINV
  exact hStar_singleFrac_unique' hINV hPre

/-! Heap lookup helpers -/

private theorem lookup_addUnion_val_left {h₁ h₂ : Heap} {x : Loc} {v : Val} {p : Perm}
    (hlk : h₁.lookup x = some (v, p)) :
    ∃ p', (h₁.addUnion h₂).lookup x = some (v, p') := by
  simp only [Heap.lookup_addUnion, hlk]
  rcases h₂.lookup x with _ | ⟨_, p₂⟩
  · exact ⟨p, rfl⟩
  · exact ⟨p + p₂, rfl⟩

private theorem lookup_addUnion_val_right {h₁ h₂ : Heap} {x : Loc} {v : Val} {p : Perm}
    (hdisj : h₁.Disjoint h₂) (hlk : h₂.lookup x = some (v, p)) :
    ∃ p', (h₁.addUnion h₂).lookup x = some (v, p') := by
  simp only [Heap.lookup_addUnion, hlk]
  rcases eq₁ : h₁.lookup x with _ | ⟨v₁, p₁⟩
  · exact ⟨p, rfl⟩
  · have ⟨hval, _⟩ := hdisj x v₁ p₁ v p eq₁ hlk
    exact ⟨p₁ + p, hval ▸ rfl⟩

private theorem option_any_val {v : Val} {p : Perm} :
    (some (v, p) : Option HeapVal).any (·.1 = v) := by
  simp [Option.any]

private theorem option_any_eq {v w : Val} {p : Perm}
    (hany : (some (v, p) : Option HeapVal).any (·.1 = w)) : w = v := by
  simp [Option.any] at hany; grind

private theorem option_any_unique {h : Heap} {x : Loc} {v w : Val} {p : Perm}
    (hlk : h.lookup x = some (v, p))
    (hany : (h.lookup x).any (·.1 = w)) : w = v := by
  rw [hlk] at hany; simp [Option.any] at hany; grind

/-! inc_t0 spec -/

private theorem HeapM.read_spec_eq (x : Loc) (v : Val) :
    ⦃ x ↦ v ⦄
    HeapM.read x
    ⦃ r, ⌜r = v⌝ʰ ∗ (x ↦ v) ⦄ := by
  -- Strengthen `HeapM.read_spec` to record the returned value.
  -- (The proof is essentially the same as `HeapM.read_spec` but keeps the equality.)
  simp [HeapM.read]
  apply Triple.iff.mpr
  unfold wp wpTrans
  simp_all [instWPMonadHeapMHPropNil]
  apply hForall_intro
  intro H
  apply entails_hWand
  intro heap HH
  simp [HeapM.pickSuchThat]
  constructor
  · refine ⟨v, ?_⟩
    -- Show the stored value is readable.
    simp_all [hStar]
    cases HH with
    | intro h₁ h₂ hH hP hunion hdisj =>
      simp [hSingle] at hP
      cases hP
      rw [← hunion, Heap.lookup_addUnion]
      rcases eq₁ : h₁.lookup x with _ | ⟨v₁, p₁⟩
      · simp [Heap.lookup_single]
      · have eq₂ : (Heap.single x v).lookup x = some (v, 1) := by simp [Heap.lookup_single]
        have ⟨hval, _⟩ := hdisj x v₁ p₁ v 1 eq₁ eq₂
        subst hval
        simp [eq₂]
  · intro r hP
    -- Uniqueness: any readable value must equal the stored one.
    have hr : r = v := by
      simp_all [hStar]
      cases HH with
      | intro h₁ h₂ hTrue hPt hunion hdisj =>
        cases hPt
        rw [← hunion] at hP
        simp [Option.any, Heap.lookup] at hP
        rcases eq₁ : h₁.lookup x with _ | ⟨v₁, p₁⟩
        · have h₁x : h₁ x = none := eq₁
          have key : h₁.addUnion (Heap.single x v) x = some (v, 1) := by
            simp [Heap.addUnion, Heap.single, h₁x]
          rw [key] at hP
          simp at hP
          grind
        · have eq₂ : (Heap.single x v).lookup x = some (v, 1) := by
            simp [Heap.lookup_single]
          have ⟨hval, _⟩ := hdisj x v₁ p₁ v 1 eq₁ eq₂
          have h₁x : h₁ x = some (v₁, p₁) := eq₁
          have key : h₁.addUnion (Heap.single x v) x = some (v₁, p₁ + 1) := by
            simp [Heap.addUnion, Heap.single, h₁x]
          rw [key] at hP
          simp at hP
          grind
    -- Return the framed resources and record `r = v`.
    refine hStar'.intro ∅ heap ?_ HH (Heap.empty_addUnion heap) (Heap.Disjoint.empty_left heap)
    · exact hPure'.intro (by simpa [hr])

theorem inc_t0_spec (c : Counter) (ot1 : Val) (wf : Counter.WF c) :
    ⦃ c.ct1 ↦[halfPerm] ot1 ⦄
    inc_t0 c
    ⦃ _, c.ct1 ↦[halfPerm] (ot1 + 1) ⦄ := by
  -- Prove this compositionally using the existing HeapM specs, avoiding the fully-unfolded wp proof.
  -- The key steps are:
  -- 1) inhale `guard_INV_ex`, 2) increment `cval`, 3) increment `ct1`,
  -- 4) re-establish `guard_INV_ex` and exhale it, returning our half-permission on `ct1`.
  --
  -- We keep the guard invariant witnesses explicit in the intermediate assertions.
  let State (vv v2 : Val) : hProp :=
    (((c.cval ↦ vv) ∗ (c.ct1 ↦ ot1)) ∗ (c.ct2 ↦[halfPerm] v2)) ∗ ⌜vv = ot1 + v2⌝ʰ
  let S0 : hProp := ∃ʰ vv, ∃ʰ v2, State vv v2

  -- Inhale the invariant and immediately combine it with our half-permission to obtain `S0`.
  have h_inhale' :
      ⦃ c.ct1 ↦[halfPerm] ot1 ⦄
      HeapM.inhale (guard_INV_ex c)
      ⦃ _, (c.ct1 ↦[halfPerm] ot1) ∗ guard_INV_ex c ⦄ := by
    -- Frame `HeapM.inhale_spec` with our precondition.
    have h0 :
        ⦃ (c.ct1 ↦[halfPerm] ot1) ∗ ∅ ⦄
        HeapM.inhale (guard_INV_ex c)
        ⦃ _, (c.ct1 ↦[halfPerm] ot1) ∗ guard_INV_ex c ⦄ := by
      simpa using
        (HeapM.frame (H := c.ct1 ↦[halfPerm] ot1) (pre := ∅)
          (post := fun _ => guard_INV_ex c) (x := HeapM.inhale (guard_INV_ex c))
          (HeapM.inhale_spec (guard_INV_ex c)))
    -- Simplify away the trailing `∗ ∅` in the precondition.
    refine HeapM.consequence (x := HeapM.inhale (guard_INV_ex c))
      (pre := c.ct1 ↦[halfPerm] ot1) (pre' := (c.ct1 ↦[halfPerm] ot1) ∗ ∅)
      (post := fun _ => (c.ct1 ↦[halfPerm] ot1) ∗ guard_INV_ex c)
      (post' := fun _ => (c.ct1 ↦[halfPerm] ot1) ∗ guard_INV_ex c) ?_ (by intro _; rfl) h0
    exact hStar_empty_intro

  have h_unpack :
      (c.ct1 ↦[halfPerm] ot1) ∗ guard_INV_ex c ⊑ S0 := by
    intro heap hHG
    rcases hHG with ⟨h_ot1, h_ginv, hOt1, hGex, hunion, hdisj⟩
    rcases hGex with ⟨vv, ⟨v1, ⟨v2, hINV⟩⟩⟩
    -- Unpack `guard_INV` into its heap components.
    unfold guard_INV at hINV
    rcases hINV with ⟨h_12p, h_t2, h12p, ht2, hu_outer, hd_outer⟩
    rcases h12p with ⟨h_12, h_pure, h12, hpure, hu_mid, hd_mid⟩
    rcases h12 with ⟨h_cv, h_t1, hcv, ht1, hu_inner, hd_inner⟩
    cases hcv
    cases ht1
    cases ht2
    cases hpure
    rename_i hinv_eq
    -- Compute lookups on `ct1` in both halves and use disjointness to pin `v1 = ot1`.
    have hlk_ot1 : h_ot1.lookup c.ct1 = some (ot1, halfPerm.1) := by
      simpa [Heap.lookup_singleFrac] using (Heap.lookup_singleFrac c.ct1 ot1 halfPerm.1)
    -- `h_t1` is the ct1-half from the invariant.
    have hlk_t1 : h_t1.lookup c.ct1 = some (v1, halfPerm.1) := by
      simpa [Heap.lookup_singleFrac] using (Heap.lookup_singleFrac c.ct1 v1 halfPerm.1)
    -- Lift `hlk_t1` to a lookup in `h_ginv` via the union equalities.
    have hlk_ginv : h_ginv.lookup c.ct1 = some (v1, halfPerm.1) := by
      -- Simplify the union structure of `h_ginv`.
      -- `h_pure = ∅`, so `h_12p = h_12`.
      have : h_pure = (∅ : Heap) := rfl
      subst this
      simp [Heap.addUnion_empty] at hu_mid
      subst hu_mid
      -- Now `h_12p = h_12` and `h_ginv = h_12.addUnion h_t2`.
      -- `h_12 = h_cv.addUnion h_t1`.
      -- Use lookup simp lemmas + wf to eliminate the other components at `ct1`.
      -- Note: `c.ct2 ≠ c.ct1` and `c.cval ≠ c.ct1`.
      have hne_val : c.cval ≠ c.ct1 := wf.val_ne_t1
      have hne_t2 : c.ct2 ≠ c.ct1 := wf.t1_ne_t2.symm
      -- Rewrite `h_ginv` using the equalities.
      -- After `cases` above, `h_cv = Heap.single c.cval vv`, `h_t1 = Heap.singleFrac c.ct1 v1 halfPerm.1`,
      -- and `h_t2 = Heap.singleFrac c.ct2 v2 halfPerm.1`.
      -- So we can compute the lookup directly.
      -- First, rewrite `h_12`.
      have : h_12.lookup c.ct1 = some (v1, halfPerm.1) := by
        -- h_12 = h_cv ∪ h_t1
        -- at ct1, h_cv is empty, h_t1 is present.
        -- This is definitional after `subst hu_inner`.
        -- Use `hu_inner` to rewrite h_12.
        have := congrArg (fun h => h.lookup c.ct1) hu_inner
        -- simp the RHS lookup
        simp [Heap.lookup_addUnion, Heap.lookup_single_ne hne_val, hlk_t1] at this
        exact this.symm
      -- Now lift to h_ginv using hu_outer and show h_t2 doesn't affect ct1.
      have := congrArg (fun h => h.lookup c.ct1) hu_outer
      simp [Heap.lookup_addUnion, this, Heap.lookup_singleFrac_ne hne_t2] at this
      exact this.symm
    have ⟨hval, _hperm⟩ := hdisj c.ct1 ot1 halfPerm.1 v1 halfPerm.1 hlk_ot1 hlk_ginv
    have hv1 : v1 = ot1 := hval.symm
    subst hv1
    -- Build the target state on `heap` by re-associating the existing heap decomposition.
    refine hExists'.intro vv (hExists'.intro v2 ?_)
    -- `State vv v2` holds on `heap` by combining the two ct1 halves into a full points-to.
    -- We construct it directly using `hStar'.intro` on the existing component heaps.
    -- First show `c.ct1 ↦ ot1` holds on `h_ot1.addUnion h_t1` using `full_is_half_half`.
    have hct1_full : (c.ct1 ↦ ot1) (h_ot1.addUnion h_t1) := by
      -- Rewrite full points-to into two halves.
      rw [full_is_half_half]
      exact hStar'.intro h_ot1 h_t1 hOt1 (by simpa using hSingleFrac'.intro)
        rfl (by
          -- disjointness between the two halves follows from `hdisj` and the union equalities
          -- (at `ct1` both halves agree and permissions add to 1).
          intro x v₁ p₁ v₂' p₂' eq₁ eq₂
          -- Both heaps are single-frac at `ct1`; disjointness is straightforward by cases on `x = ct1`.
          by_cases hx : x = c.ct1
          · subst hx
            simp [Heap.lookup_singleFrac] at eq₁ eq₂
            obtain ⟨rfl, rfl⟩ := eq₁
            obtain ⟨rfl, rfl⟩ := eq₂
            constructor <;> simp [halfPerm, Perm.add]
          · have hne : c.ct1 ≠ x := by exact hx
            simp [Heap.lookup_singleFrac_ne hne] at eq₁)
    -- Now assemble `State vv v2` from `h_cv`, `h_ot1.addUnion h_t1`, `h_t2`, and the pure equation.
    -- Use the existing disjointness/union structure to show these pieces union to `heap`.
    -- We reuse `hunion : h_ot1.addUnion h_ginv = heap`.
    -- The heap of `h_ginv` is `((h_cv.addUnion h_t1).addUnion h_t2)`.
    -- Associate to make `h_ot1.addUnion h_t1` explicit.
    -- First, construct the left part `((c.cval ↦ vv) ∗ (c.ct1 ↦ ot1))` on `h_cv.addUnion (h_ot1.addUnion h_t1)`.
    refine (show State vv v2 heap from by
      -- Expand `State`.
      dsimp [State]
      -- Build `(((c.cval ↦ vv) ∗ (c.ct1 ↦ ot1)) ∗ (c.ct2 ↦[halfPerm] v2)) ∗ ⌜vv = ot1 + v2⌝ʰ`
      -- on the full heap by choosing the same component heaps.
      refine hStar'.intro ((h_cv.addUnion (h_ot1.addUnion h_t1)).addUnion h_t2) ∅ ?_ (hPure'.intro (by simpa [hinv_eq, Int.add_assoc, Int.add_left_comm, Int.add_comm])) ?_ ?_
      · refine hStar'.intro (h_cv.addUnion (h_ot1.addUnion h_t1)) h_t2 ?_ (by simpa using hSingleFrac'.intro) rfl ?_
        · refine hStar'.intro h_cv (h_ot1.addUnion h_t1) (by exact hSingle'.intro) hct1_full rfl ?_
          -- disjointness between cval and ct1 heaps follows from wf and the fact these are singletons.
          intro x v₁ p₁ v₂' p₂' eq₁ eq₂
          by_cases hx : x = c.cval
          · subst hx
            have hne : c.ct1 ≠ c.cval := wf.val_ne_t1.symm
            simp [Heap.lookup_single, Heap.lookup_singleFrac_ne hne] at eq₂
          · have hne : c.cval ≠ x := by exact hx
            simp [Heap.lookup_single_ne hne] at eq₁
        -- disjointness between `(h_cv ∪ (h_ot1 ∪ h_t1))` and `h_t2` follows from wf (distinct locations).
        intro x v₁ p₁ v₂' p₂' eq₁ eq₂
        have hne_t2_val : c.ct2 ≠ c.cval := wf.val_ne_t2.symm
        have hne_t2_t1 : c.ct2 ≠ c.ct1 := wf.t1_ne_t2.symm
        -- Lookup in `h_t2` forces `x = ct2`; then the left lookup is none.
        by_cases hx : x = c.ct2
        · subst hx
          simp [Heap.lookup_singleFrac] at eq₂
          rcases eq₂ with ⟨rfl, rfl⟩
          -- Left heap has no entry at ct2.
          simp [Heap.lookup_addUnion, Heap.lookup_single_ne hne_t2_val, Heap.lookup_singleFrac_ne hne_t2_t1] at eq₁
        · have hne : c.ct2 ≠ x := by exact hx
          simp [Heap.lookup_singleFrac_ne hne] at eq₂
      · -- Union equality: the chosen heaps add up to `heap`.
        -- We know `heap = h_ot1.addUnion h_ginv` from `hunion`, and `h_ginv` is built from `h_cv`, `h_t1`, `h_t2`.
        -- Reassociate to match our construction.
        -- First rewrite `heap` using `hunion`.
        -- Then rewrite `h_ginv` using `hu_outer`, `hu_inner`.
        -- Finally use associativity/commutativity of `addUnion`.
        -- This is a bit of arithmetic on unions.
        -- Start:
        --   heap = h_ot1 ∪ ((h_cv ∪ h_t1) ∪ h_t2)
        --   = ((h_cv ∪ (h_ot1 ∪ h_t1)) ∪ h_t2)
        -- using assoc/comm.
        -- We'll do it by ext on lookups.
        apply Heap.ext_lookup; intro x
        -- Rewrite heap lookup using `hunion` and `hu_outer`/`hu_inner`.
        -- `h_pure` was eliminated, so `h_ginv = (h_12.addUnion h_t2)` with `h_12 = h_cv.addUnion h_t1`.
        -- We'll use these equalities in simp.
        -- First, turn `hunion` into a lookup equality.
        have hheap : heap.lookup x = (h_ot1.addUnion h_ginv).lookup x := by
          simpa [hunion] using congrArg (fun h => h.lookup x) hunion
        -- Now expand `h_ginv` via `hu_outer` and `hu_inner`.
        have hg : h_ginv.lookup x = ((h_cv.addUnion h_t1).addUnion h_t2).lookup x := by
          -- `hu_mid` already simplified, so `h_12p = h_12`.
          -- Use `hu_outer` and `hu_inner`.
          simpa [hu_outer, hu_inner] using congrArg (fun h => h.lookup x) (Eq.refl h_ginv)
        -- Finish by simp using associativity.
        -- (We avoid rewriting `h_ginv` by simp; instead just simp the explicit expression.)
        -- This is crude but works.
        simp [Heap.lookup_addUnion, hheap, Heap.addUnion_assoc]
      · -- Disjointness between the big heap and ∅.
        exact Heap.Disjoint.empty_right _
    )

  have h_inhale : ⦃ c.ct1 ↦[halfPerm] ot1 ⦄ HeapM.inhale (guard_INV_ex c) ⦃ _, S0 ⦄ := by
    refine HeapM.consequence (x := HeapM.inhale (guard_INV_ex c))
      (pre := c.ct1 ↦[halfPerm] ot1) (pre' := c.ct1 ↦[halfPerm] ot1)
      (post := fun _ => S0)
      (post' := fun _ => (c.ct1 ↦[halfPerm] ot1) ∗ guard_INV_ex c)
      (by intro _; exact PartialOrder.rel_refl) (by intro _; exact h_unpack) h_inhale'

  -- Now chain the program using `Triple.bind`.
  simp [inc_t0]
  refine Triple.bind (x := HeapM.inhale (guard_INV_ex c)) (f := fun _ => _)
    (mid := fun _ => S0) h_inhale ?_
  intro _u
  -- Read `cval` to obtain `vv`.
  refine Triple.bind (x := HeapM.read c.cval) (f := fun vv => _)
    (mid := fun vv => ∃ʰ v2, State vv v2) ?_ ?_
  · -- `S0` provides some stored `vv`; `read` returns that `vv` and preserves the heap.
    -- We implement this by unpacking the existentials and using `HeapM.read_spec_eq` framed by the rest.
    apply Triple.iff.mpr
    intro heap hS0
    rcases hS0 with ⟨vv, ⟨v2, hSt⟩⟩
    -- Frame the rest around the read.
    have hread_base : ⦃ c.cval ↦ vv ⦄ HeapM.read c.cval ⦃ r, ⌜r = vv⌝ʰ ∗ (c.cval ↦ vv) ⦄ :=
      HeapM.read_spec_eq (x := c.cval) (v := vv)
    -- Use consequence + frame to lift to `State`.
    -- (We rely on `HeapM.frame` and then destruct the post to extract the preserved `State`.)
    -- For simplicity, go back to the definition via `Triple.iff` and reuse `hread_base`.
    exact (Triple.iff.mp (HeapM.frame (H := ((c.ct1 ↦ ot1) ∗ (c.ct2 ↦[halfPerm] v2)) ∗ ⌜vv = ot1 + v2⌝ʰ)
      (pre := c.cval ↦ vv) (post := fun _ => (⌜_ = _⌝ʰ ∗ (c.cval ↦ vv))) (x := HeapM.read c.cval) hread_base)) heap ?_
  · intro vv
    -- Assign `cval := vv+1`.
    refine Triple.bind (x := HeapM.assign c.cval (vv + 1)) (f := fun _ => _)
      (mid := fun _ => ∃ʰ v2, (((c.cval ↦ (vv + 1)) ∗ (c.ct1 ↦ ot1)) ∗ (c.ct2 ↦[halfPerm] v2)) ∗ ⌜vv = ot1 + v2⌝ʰ) ?_ ?_
    · sorry
    · intro _u2
      -- Read ct1, then assign ct1 := v1+1, then exhale invariant.
      sorry

/-! inc_t1 spec (symmetric) -/

theorem inc_t1_spec (c : Counter) (ot2 : Val) (wf : Counter.WF c) :
    ⦃ c.ct2 ↦[halfPerm] ot2 ⦄
    inc_t1 c
    ⦃ _, c.ct2 ↦[halfPerm] (ot2 + 1) ⦄ := by
  sorry

/-! main program -/

def main_prog (c : Counter) : HeapM Unit := do
  HeapM.assign c.cval 0
  HeapM.assign c.ct1  0
  HeapM.assign c.ct2  0
  HeapM.exhale (guard_INV c 0 0 0)
  HeapM.exhale (inc_PRE c false 0)
  HeapM.exhale (inc_PRE c true  0)
  HeapM.inhale (inc_POST c false 0)
  HeapM.inhale (inc_POST c true  0)
  HeapM.inhale (guard_INV_ex c)


theorem main_spec (c : Counter) (wf : Counter.WF c) :
    ⦃ ((c.cval ↦ 0) ∗ (c.ct1 ↦ 0)) ∗ (c.ct2 ↦ 0) ⦄
    main_prog c
    ⦃ _, ∃ʰ vv, (c.cval ↦ vv) ∗ ⌜vv = 2⌝ʰ ⦄ := by
   apply Triple.iff.mpr
   unfold wp wpTrans main_prog
   simp_all [instWPMonadHeapMHPropNil]
   apply hForall_intro
   intro H
   apply entails_hWand
   simp [Bind.bind, HeapM.bind, HeapM.inhale, HeapM.exhale, HeapM.assign, fullPerm, inc_PRE, guard_INV, inc_POST, guard_INV_ex]
