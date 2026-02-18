import Loom.WP.Basic

open Lean.Order

namespace Loom.WP

universe u v
variable {m : Type u → Type v}

/-! ## Basic WPMonad simp lemmas -/

@[simp]
theorem pure_wp [Monad m] [CompleteLattice l] [WPMonad m l es]
    (a : α) (post : α → l) (epost : EPost es) :
  post a ⊑ wp (pure (f := m) a) post epost :=
  WPMonad.wp_pure a post epost

@[simp]
theorem bind_wp [Monad m] [CompleteLattice l] [WPMonad m l es]
    (x : m α) (f : α → m β) (post : β → l) (epost : EPost es) :
  wp x (fun a => wp (f a) post epost) epost ⊑ wp (x >>= f) post epost :=
  WPMonad.wp_bind x f post epost

@[simp]
theorem map_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l es]
    (f : α → β) (x : m α) (post : β → l) (epost : EPost es) :
  wp x (fun a => post (f a)) epost ⊑ wp (f <$> x) post epost :=
  WPMonad.wp_map f x post epost

@[simp]
theorem seq_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l es]
    (f : m (α → β)) (x : m α) (post : β → l) (epost : EPost es) :
  wp f (fun g => wp x (fun a => post (g a)) epost) epost ⊑ wp (f <*> x) post epost :=
  WPMonad.wp_seq f x post epost

/-! ## Reader / State simp lemmas -/

@[simp]
theorem read_ReaderT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l es]
    (post : ρ → ρ → l) (epost : EPost es) :
  (fun r => post r r) ⊑ wp (MonadReaderOf.read : ReaderT ρ m ρ) post epost := by
  intro r
  simpa [MonadReaderOf.read] using
    (WPMonad.wp_pure (m := m) (x := r) (post := fun a => post a r) (epost := epost))

@[simp]
theorem adapt_ReaderT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l es]
    (f : ρ → ρ') (x : ReaderT ρ' m α) (post : α → ρ → l) (epost : EPost es) :
  wp (ReaderT.adapt f x : ReaderT ρ m α) post epost =
    fun r => wp x (fun a _ => post a r) epost (f r) := rfl

@[simp]
theorem get_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l es]
    (post : σ → σ → l) (epost : EPost es) :
  (fun s => post s s) ⊑ wp (MonadStateOf.get : StateT σ m σ) post epost := by
  intro s
  simpa [MonadStateOf.get] using
    (WPMonad.wp_pure (m := m) (x := (s, s))
      (post := fun x => post x.fst x.snd) (epost := epost))

@[simp]
theorem set_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l es]
    (x : σ) (post : PUnit → σ → l) (epost : EPost es) :
  (fun _ => post ⟨⟩ x) ⊑ wp (MonadStateOf.set x : StateT σ m PUnit) post epost := by
  intro s
  simpa [MonadStateOf.set] using
    (WPMonad.wp_pure (m := m) (x := (PUnit.unit, x))
      (post := fun x => post x.fst x.snd) (epost := epost))

@[simp]
theorem modifyGet_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l es]
    (f : σ → α × σ) (post : α → σ → l) (epost : EPost es) :
  (fun s => post (f s).1 (f s).2) ⊑ wp (MonadStateOf.modifyGet f : StateT σ m α) post epost := by
  intro s
  simpa [MonadStateOf.modifyGet] using
    (WPMonad.wp_pure (m := m) (x := f s)
      (post := fun x => post x.fst x.snd) (epost := epost))

@[simp]
theorem get_EStateM_wp (post : σ → σ → Prop) (epost : EPost [ε → σ → Prop]) :
  wp (MonadStateOf.get : EStateM ε σ σ) post epost = fun s => post s s := by
  funext s
  simp only [wp, WPMonad.wpImpl, MonadStateOf.get, EStateM.get]

@[simp]
theorem set_EStateM_wp (x : σ) (post : PUnit → σ → Prop) (epost : EPost [ε → σ → Prop]) :
  wp (MonadStateOf.set x : EStateM ε σ PUnit) post epost = fun _ => post ⟨⟩ x := by
  funext s
  simp only [wp, WPMonad.wpImpl, MonadStateOf.set, EStateM.set]

@[simp]
theorem modifyGet_EStateM_wp (f : σ → α × σ) (post : α → σ → Prop) (epost : EPost [ε → σ → Prop]) :
  wp (MonadStateOf.modifyGet f : EStateM ε σ α) post epost = fun s => post (f s).1 (f s).2 := by
  funext s
  simp only [wp, WPMonad.wpImpl, MonadStateOf.modifyGet, EStateM.modifyGet]

/-! ## Except / throw / tryCatch simp lemmas -/

@[simp]
theorem throwThe_wp [MonadExceptOf ε m] [Monad m] [CompleteLattice l] [WPMonad m l es]
    (err : ε) (post : α → l) (epost : EPost es) :
  wp (throwThe ε err : m α) post epost = wp (MonadExceptOf.throw err : m α) post epost := rfl

@[simp]
theorem throw_Except_wp (e : ε) (post : α → Prop) (epost : EPost [ε → Prop]) :
  wp (MonadExceptOf.throw e : Except ε α) post epost = epost.head e := by
  simp [wp, WPMonad.wpImpl]

@[simp]
theorem throw_ExceptT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l es]
    (err : ε) (post : α → l) (epost : EPost ((ε → l) :: es)) :
  epost.head err ⊑ wp (MonadExceptOf.throw err : ExceptT ε m α) post epost := by
  simpa [MonadExceptOf.throw, pushExcept.post] using
    (WPMonad.wp_pure (m := m) (x := Except.error err)
      (post := pushExcept.post post epost) (epost := epost.tail))

@[simp]
theorem throw_EStateM_wp (e : ε) (post : α → σ → Prop) (epost : EPost [ε → σ → Prop]) :
  wp (MonadExceptOf.throw e : EStateM ε σ α) post epost = fun s => epost.head e s := by
  funext s
  simp only [wp, WPMonad.wpImpl, MonadExceptOf.throw, EStateM.throw]

@[simp]
theorem throw_Option_wp (e : PUnit) (post : α → Prop) (epost : EPost [Prop]) :
  wp (MonadExceptOf.throw e : Option α) post epost = epost.head := by
  cases e
  simp only [wp, MonadExceptOf.throw]
  rfl

@[simp]
theorem tryCatch_MonadExcept_wp [MonadExceptOf ε m] [Monad m] [CompleteLattice l] [WPMonad m l es]
    (x : m α) (h : ε → m α) (post : α → l) (epost : EPost es) :
  wp (tryCatch x h : m α) post epost = wp (MonadExceptOf.tryCatch x h : m α) post epost := rfl

@[simp]
theorem tryCatchThe_wp [MonadExceptOf ε m] [Monad m] [CompleteLattice l] [WPMonad m l es]
    (x : m α) (h : ε → m α) (post : α → l) (epost : EPost es) :
  wp (tryCatchThe ε x h : m α) post epost = wp (MonadExceptOf.tryCatch x h : m α) post epost := rfl

@[simp]
theorem tryCatch_Except_wp (x : Except ε α) (h : ε → Except ε α) (post : α → Prop) (epost : EPost [ε → Prop]) :
  wp (MonadExceptOf.tryCatch x h : Except ε α) post epost =
    wp x post epost⟨fun e => wp (h e) post epost⟩ := by
  cases x <;> rfl

-- TODO: Upstream
@[simp] theorem _root_.ExceptT.run_tryCatch [Monad m] [LawfulMonad m] (x : ExceptT ε m α) (h : ε → ExceptT ε m α) :
  (tryCatch x h : ExceptT ε m α).run =
    (do
      let r ← x.run
      match r with
      | .ok a => pure (.ok a)
      | .error e => (h e).run) := by
  simp only [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch, ExceptT.run_mk]
  rfl

@[simp]
theorem tryCatch_ExceptT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l es]
    (x : ExceptT ε m α) (h : ε → ExceptT ε m α) (post : α → l) (epost : EPost ((ε → l) :: es)) :
  wp x post (EPost.cons (fun e => wp (h e) post epost) epost.tail) ⊑
    wp (MonadExceptOf.tryCatch x h : ExceptT ε m α) post epost := by
  change _ ⊑ wp (tryCatch x h : ExceptT ε m α) _ _
  simp only [ExceptT.apply_wp, ExceptT.run_tryCatch]
  apply PartialOrder.rel_trans; rotate_left
  · apply WPMonad.wp_bind
  · apply WPMonad.wp_cons
    intro r; cases r with
    | ok a => simpa [pushExcept.post] using
        (WPMonad.wp_pure (m := m) (x := Except.ok a)
          (post := pushExcept.post post epost) (epost := epost.tail))
    | error _ => exact PartialOrder.rel_refl

@[simp]
theorem tryCatch_EStateM_wp (x : EStateM ε σ α) (h : ε → EStateM ε σ α)
    (post : α → σ → Prop) (epost : EPost [ε → σ → Prop]) :
  wp (MonadExceptOf.tryCatch x h : EStateM ε σ α) post epost =
    fun s => wp x post epost⟨fun e s' => wp (h e) post epost s'⟩ s := by
  funext s
  simp only [wp, WPMonad.wpImpl, MonadExceptOf.tryCatch, EStateM.tryCatch]
  cases (x s) <;> simp
  rfl

/-! ## Additional state operation lemmas -/

@[simp]
theorem getThe_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l es]
    (post : σ → σ → l) (epost : EPost es) :
  wp (getThe σ : StateT σ m σ) post epost = wp (MonadStateOf.get : StateT σ m σ) post epost := rfl

@[simp]
theorem modifyThe_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l es]
    (f : σ → σ) (post : PUnit → σ → l) (epost : EPost es) :
  wp (modifyThe σ f : StateT σ m PUnit) post epost =
    wp (MonadStateOf.modifyGet fun s => (⟨⟩, f s) : StateT σ m PUnit) post epost := rfl

@[simp]
theorem modifyGetThe_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l es]
    (f : σ → α × σ) (post : α → σ → l) (epost : EPost es) :
  wp (modifyGetThe σ f : StateT σ m α) post epost =
    wp (MonadStateOf.modifyGet f : StateT σ m α) post epost := rfl

/-! ## MonadLift simp lemmas -/

@[simp]
theorem monadLift_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l es]
    (x : m α) (post : α → σ → l) (epost : EPost es) :
  (fun s => wp x (fun a => post a s) epost) ⊑
    wp (MonadLift.monadLift x : StateT σ m α) post epost := by
  intro s
  simp only [wp, MonadLift.monadLift]
  apply PartialOrder.rel_trans; rotate_left
  · apply WPMonad.wp_bind
  · apply WPMonad.wp_cons (m := m)
    intro a
    simpa using
      (WPMonad.wp_pure (m := m) (x := (a, s))
        (post := fun x => post x.fst x.snd) (epost := epost))

@[simp]
theorem monadLift_ReaderT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l es]
    (x : m α) (post : α → ρ → l) (epost : EPost es) :
  wp (MonadLift.monadLift x : ReaderT ρ m α) post epost = fun r => wp x (fun a => post a r) epost := rfl

@[simp]
theorem monadLift_ExceptT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l es]
    (x : m α) (post : α → l) (epost : EPost ((ε → l) :: es)) :
  wp x post epost.tail ⊑ wp (MonadLift.monadLift x : ExceptT ε m α) post epost := by
  simp only [wp, MonadLift.monadLift, ExceptT.lift, ExceptT.mk]
  apply PartialOrder.rel_trans; rotate_left
  · exact WPMonad.wp_map (m := m) Except.ok x _ _
  · exact PartialOrder.rel_refl

@[simp]
theorem lift_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l es]
    (x : m α) (post : α → σ → l) (epost : EPost es) :
  wp (StateT.lift x : StateT σ m α) post epost = wp (MonadLift.monadLift x : StateT σ m α) post epost := rfl

@[simp]
theorem lift_ExceptT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l es]
    (x : m α) (post : α → l) (epost : EPost ((ε → l) :: es)) :
  wp (ExceptT.lift x : ExceptT ε m α) post epost = wp (MonadLift.monadLift x : ExceptT ε m α) post epost := rfl

end Loom.WP
