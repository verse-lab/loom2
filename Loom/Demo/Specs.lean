import Loom.Triple.Basic
import Loom.Tactic.VCGen

open Lean.Order Std.Do'

@[lspec]
theorem Spec.monadLift_StateT_demo {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    (x : m α) (post : α → σ → Pred) (epost : EPred) :
    Triple (fun s => wp x (fun a => post a s) epost)
      (monadLift x : StateT σ m α) post epost := by
  rw [Triple.iff]
  exact WP.monadLift_StateT_wp x post

@[lspec]
theorem Spec.modify_StateT {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    (f : σ → σ) (post : PUnit → σ → Pred) (epost : EPred) :
    Triple (fun s => post ⟨⟩ (f s))
      (modify f : StateT σ m PUnit) post epost := by
  rw [Triple.iff]
  intro s
  simpa [WP.modify_StateT_wp, MonadStateOf.modifyGet] using
    (WP.wp_pure (m := m) (x := (PUnit.unit, f s))
      (post := fun x => post x.fst x.snd) (epost := epost))

@[lspec]
theorem Spec.modify_ExpetT {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [MonadState σ m] [MonadState σ (ExceptT ε m)]
    [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    (f : σ → σ) (post : PUnit → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (wp (MonadLift.monadLift (n := ExceptT ε m) (modify f : m PUnit)) post epost)
      (modify (m := ExceptT ε m) f) post epost := by
  sorry

@[lspec]
theorem Spec.modify_ExpetT' {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [MonadStateOf σ m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    (f : σ → σ) (post : PUnit → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (wp (MonadLift.monadLift (n := ExceptT ε m) (modifyThe σ f : m PUnit)) post epost)
      (modifyThe σ f : ExceptT ε m PUnit) post epost := by
  sorry

@[lspec]
theorem Spec.modify_ReaderT {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [MonadState σ m] [MonadState σ (ReaderT ρ m)]
    [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    (f : σ → σ) (post : PUnit → ρ → Pred) (epost : EPred) :
    Triple (wp (MonadLift.monadLift (n := ReaderT ρ m) (modify f : m PUnit)) post epost)
      (modify (m := ReaderT ρ m) f) post epost := by
  sorry

@[lspec]
theorem Spec.read_ReaderT {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    (post : ρ → ρ → Pred) (epost : EPred) :
    Triple (fun r => post r r)
      (read : ReaderT ρ m ρ) post epost := by
  rw [Triple.iff]
  exact WP.read_ReaderT_wp post epost

@[lspec]
theorem Spec.read_ExpetT {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [MonadReaderOf ρ m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    (post : ρ → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (wp (MonadLift.monadLift (n := ExceptT ε m) (read : m ρ)) post epost)
      (read : ExceptT ε m ρ) post epost := by
  sorry

@[lspec]
theorem Spec.read_ExpetT' {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [MonadReaderOf ρ m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    (post : ρ → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (wp (MonadLift.monadLift (n := ExceptT ε m) (MonadReaderOf.read : m ρ)) post epost)
      (MonadReaderOf.read : ExceptT ε m ρ) post epost := by
  sorry

@[lspec]
theorem Spec.throwThe_ExpetT {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    (err : ε) (post : α → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (epost.head err)
      (throwThe ε err : ExceptT ε m α) post epost := by
  sorry

@[lspec]
theorem Spec.throwThe_ExpetT' {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    (err : ε) (post : α → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (epost.head err)
      (MonadExceptOf.throw err : ExceptT ε m α) post epost := by
  sorry

@[lspec]
theorem Spec.throwThe_ReaderT {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [MonadExceptOf ε m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    (err : ε) (post : α → ρ → Pred) (epost : EPred) :
    Triple (fun r => wp (throwThe ε err : m α) (fun a => post a r) epost)
      (throwThe ε err : ReaderT ρ m α) post epost := by
  sorry

@[lspec]
theorem Spec.get_ExpetT {Pred EPred : Type u} [Monad m] [MonadStateOf σ m] [Assertion Pred] [Assertion EPred]
  [WP m Pred EPred] (post : σ → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (wp (MonadLift.monadLift (n := ExceptT ε m) (MonadStateOf.get : m σ)) post epost)
      (get : ExceptT ε m σ) post epost := sorry

@[lspec]
theorem Spec.get_ExpetT' {Pred EPred : Type u} [Monad m] [MonadStateOf σ m] [Assertion Pred] [Assertion EPred]
  [WP m Pred EPred] (post : σ → Pred) (epost : EPost.cons (ε → Pred) EPred) :
    Triple (wp (MonadLift.monadLift (n := ExceptT ε m) (MonadStateOf.get : m σ)) post epost)
      (MonadStateOf.get : ExceptT ε m σ) post epost := sorry

@[lspec]
theorem Spec.get_ReaderT {Pred EPred : Type u} [Monad m] [MonadStateOf σ m] [Assertion Pred] [Assertion EPred]
  [WP m Pred EPred] (post : σ → ρ → Pred) (epost : EPred) :
    Triple (wp (MonadLift.monadLift (n := ReaderT ρ m) (MonadStateOf.get : m σ)) post epost)
      (MonadStateOf.get : ReaderT ρ m σ) post epost := sorry
