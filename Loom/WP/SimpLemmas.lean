import Loom.WP.Basic

open Lean.Order

namespace Loom.WP

universe u v
variable {m : Type u → Type v}

/-!
# Simp lemmas for weakest preconditions

This file provides simp lemmas for simplifying weakest precondition expressions.
Unlike Std/Do, we use direct function application `wp x post epost` without notation.

Some lemmas prove only one direction (`⊑`) instead of equality because our wp_bind axiom
only provides one direction.
-/

/-! ## Basic WPMonad simp lemmas -/

@[simp]
theorem pure_wp [Monad m] [CompleteLattice l] [WPMonad m l e] (a : α) :
  wp (pure (f:=m) a) post epost = post a := by
  exact WPMonad.wp_pure a post epost

@[simp]
theorem bind_wp [Monad m] [CompleteLattice l] [WPMonad m l e] (x : m α) (f : α → m β) :
  wp x (fun a => wp (f a) post epost) epost ⊑ wp (x >>= f) post epost := by
  exact WPMonad.wp_bind x f post epost

-- Note: wp_map and wp_seq already exist in Basic.lean but without @[simp]
-- We re-export them here with the simp attribute

@[simp]
theorem map_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (f : α → β) (x : m α) :
  wp x (fun a => post (f a)) epost ⊑ wp (f <$> x) post epost :=
  WPMonad.wp_map f x _ _

@[simp]
theorem seq_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (f : m (α → β)) (x : m α) :
  ∀ post epost, wp f (fun g => wp x (fun a => post (g a)) epost) epost ⊑ wp (f <*> x) post epost :=
  WPMonad.wp_seq f x

/-! ## Transformer .run simplification lemmas -/

@[simp]
theorem ReaderT_run_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : ReaderT ρ m α) (r : ρ) :
  wp (x.run r) post epost = wp x (fun a _ => post a) epost r := by
  rfl

@[simp]
theorem StateT_run_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : StateT σ m α) (s : σ) :
  wp (x.run s) post epost = wp x (fun a s' => post (a, s')) epost s := by
  rfl

@[simp]
theorem ExceptT_run_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : ExceptT ε m α) :
  wp (x.run) (fun r => match r with | .ok a => post a | .error e => epost.2 e) epost.1 =
    wp x post epost := by
  simp only [wp, ExceptT.run]
  rfl

@[simp]
theorem OptionT_run_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : OptionT m α) :
  wp (x.run) (fun o => match o with | some a => post a | none => epost.2) epost.1 =
    wp x post epost := by
  simp only [wp, OptionT.run]
  rfl

/-! ## MonadReaderOf simp lemmas -/

@[simp]
theorem read_ReaderT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] :
  wp (MonadReaderOf.read : ReaderT ρ m ρ) post epost = fun r => post r r := by
  funext r
  simp only [wp, MonadReaderOf.read, ReaderT.read, WPMonad.wp_pure]

@[simp]
theorem adapt_ReaderT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (f : ρ → ρ') (x : ReaderT ρ' m α) :
  wp (ReaderT.adapt f x : ReaderT ρ m α) post epost =
    fun r => wp x (fun a _ => post a r) epost (f r) := rfl

/-! ## MonadStateOf simp lemmas -/

@[simp]
theorem get_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] :
  wp (MonadStateOf.get : StateT σ m σ) post epost = fun s => post s s := by
  funext s
  simp only [wp, MonadStateOf.get, StateT.get, WPMonad.wp_pure]

@[simp]
theorem set_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : σ) :
  wp (MonadStateOf.set x : StateT σ m PUnit) post epost = fun _ => post ⟨⟩ x := by
  funext s
  simp only [wp, MonadStateOf.set, StateT.set, WPMonad.wp_pure]

@[simp]
theorem modifyGet_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (f : σ → α × σ) :
  wp (MonadStateOf.modifyGet f : StateT σ m α) post epost = fun s => post (f s).1 (f s).2 := by
  funext s
  simp only [wp, MonadStateOf.modifyGet, StateT.modifyGet, WPMonad.wp_pure]

@[simp]
theorem get_EStateM_wp :
  wp (MonadStateOf.get : EStateM ε σ σ) post epost = fun s => post s s := by
  funext s
  simp only [wp, MonadStateOf.get, EStateM.get]

@[simp]
theorem set_EStateM_wp (x : σ) :
  wp (MonadStateOf.set x : EStateM ε σ PUnit) post epost = fun _ => post ⟨⟩ x := by
  funext s
  simp only [wp, MonadStateOf.set, EStateM.set]

@[simp]
theorem modifyGet_EStateM_wp (f : σ → α × σ) :
  wp (MonadStateOf.modifyGet f : EStateM ε σ α) post epost = fun s => post (f s).1 (f s).2 := by
  funext s
  simp only [wp, MonadStateOf.modifyGet, EStateM.modifyGet]

@[simp]
theorem modify_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (f : σ → σ) :
  wp (modify f : StateT σ m PUnit) post epost =
    wp (MonadStateOf.modifyGet fun s => (⟨⟩, f s) : StateT σ m PUnit) post epost := by
  rfl

@[simp]
theorem getModify_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (f : σ → σ) :
  wp (getModify f : StateT σ m σ) post epost =
    wp (MonadStateOf.modifyGet fun s => (s, f s) : StateT σ m σ) post epost := by
  rfl

@[simp]
theorem modify_EStateM_wp (f : σ → σ) :
  wp (modify f : EStateM ε σ PUnit) post epost =
    wp (MonadStateOf.modifyGet fun s => (⟨⟩, f s) : EStateM ε σ PUnit) post epost := by
  rfl

@[simp]
theorem getModify_EStateM_wp (f : σ → σ) :
  wp (getModify f : EStateM ε σ σ) post epost =
    wp (MonadStateOf.modifyGet fun s => (s, f s) : EStateM ε σ σ) post epost := by
  rfl

/-! ## MonadExceptOf simp lemmas -/

@[simp]
theorem throw_MonadExcept_wp [MonadExceptOf ε m] [Monad m] [CompleteLattice l] [WPMonad m l e] (err : ε) :
  wp (throw err : m α) post epost =
    wp (MonadExceptOf.throw err : m α) post epost := by
  rfl

@[simp]
theorem throwThe_wp [MonadExceptOf ε m] [Monad m] [CompleteLattice l] [WPMonad m l e] (err : ε) :
  wp (throwThe ε err : m α) post epost =
    wp (MonadExceptOf.throw err : m α) post epost := by
  rfl

@[simp]
theorem throw_Except_wp (e : ε) : wp (MonadExceptOf.throw e : Except ε α) post epost = epost e := by
  simp only [wp]

@[simp]
theorem throw_ExceptT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (err : ε) :
  wp (MonadExceptOf.throw err : ExceptT ε m α) post epost = epost.2 err := by
  simp only [wp, MonadExceptOf.throw, ExceptT.mk, WPMonad.wp_pure]

@[simp]
theorem throw_EStateM_wp (e : ε) :
  wp (MonadExceptOf.throw e : EStateM ε σ α) post epost = epost e := by
  funext s
  simp only [wp, MonadExceptOf.throw, EStateM.throw]

@[simp]
theorem throw_Option_wp (e : PUnit) : wp (MonadExceptOf.throw e : Option α) post epost = epost := by
  simp only [wp, MonadExceptOf.throw]
  rfl

@[simp]
theorem throw_OptionT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (err : PUnit) :
  wp (MonadExceptOf.throw err : OptionT m α) post epost = epost.2 := by
  simp only [wp, MonadExceptOf.throw, OptionT.mk, OptionT.fail, OptionT.run, WPMonad.wp_pure]

@[simp]
theorem tryCatch_MonadExcept_wp [MonadExceptOf ε m] [Monad m] [CompleteLattice l] [WPMonad m l e] (x : m α) (h : ε → m α) :
  wp (tryCatch x h : m α) post epost =
    wp (MonadExceptOf.tryCatch x h : m α) post epost := by
  rfl

@[simp]
theorem tryCatchThe_wp [MonadExceptOf ε m] [Monad m] [CompleteLattice l] [WPMonad m l e] (x : m α) (h : ε → m α) :
  wp (tryCatchThe ε x h : m α) post epost =
    wp (MonadExceptOf.tryCatch x h : m α) post epost := by
  rfl

@[simp]
theorem tryCatch_Except_wp (x : Except ε α) (h : ε → Except ε α) :
  ∀ post (epost : ε → Prop),
  wp (MonadExceptOf.tryCatch x h : Except ε α) post epost =
    wp x post (fun e => wp (h e) post epost) := by
  simp only [wp, MonadExceptOf.tryCatch, Except.tryCatch]
  cases x <;> simp

@[simp]
theorem tryCatch_ExceptT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : ExceptT ε m α) (h : ε → ExceptT ε m α) :
  wp x post (epost.1, fun e => wp (h e) post epost) ⊑
  wp (MonadExceptOf.tryCatch x h : ExceptT ε m α) post epost
     := by
  simp only [wp, MonadExceptOf.tryCatch, ExceptT.tryCatch, ExceptT.mk]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_bind
  apply WPMonad.wp_cons; intro r; cases r <;> simp [PartialOrder.rel_refl]

@[simp]
theorem tryCatch_Option_wp (x : Option α) (h : PUnit → Option α) :
  wp (MonadExceptOf.tryCatch x h : Option α) post epost =
    wp x post (wp (h ⟨⟩) post epost) := by
  simp only [wp, MonadExceptOf.tryCatch, Option.tryCatch]
  cases x <;> simp

@[simp]
theorem tryCatch_EStateM_wp (x : EStateM ε σ α) (h : ε → EStateM ε σ α) :
  wp (MonadExceptOf.tryCatch x h : EStateM ε σ α) post epost =
    fun s => wp x post (fun e s' => wp (h e) post epost s') s := by
  funext s
  simp only [wp, MonadExceptOf.tryCatch, EStateM.tryCatch]
  cases (x s) <;> simp
  rfl

@[simp]
theorem tryCatch_OptionT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : OptionT m α) (h : PUnit → OptionT m α) :
  wp x post (epost.1, wp (h ⟨⟩) post epost) ⊑
    wp (MonadExceptOf.tryCatch x h : OptionT m α) post epost := by
  simp only [wp, MonadExceptOf.tryCatch, OptionT.tryCatch, OptionT.mk, OptionT.run]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_bind
  apply WPMonad.wp_cons (m := m); intro o; cases o with
  | some a => simp [WPMonad.wp_pure (m := m), PartialOrder.rel_refl]
  | none => exact PartialOrder.rel_refl

/-! ## Additional state operation lemmas -/

@[simp]
theorem getThe_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] :
  wp (getThe σ : StateT σ m σ) post epost =
    wp (MonadStateOf.get : StateT σ m σ) post epost := by
  rfl

@[simp]
theorem modifyThe_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (f : σ → σ) :
  wp (modifyThe σ f : StateT σ m PUnit) post epost =
    wp (MonadStateOf.modifyGet fun s => (⟨⟩, f s) : StateT σ m PUnit) post epost := by
  rfl

@[simp]
theorem modifyGetThe_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (f : σ → α × σ) :
  wp (modifyGetThe σ f : StateT σ m α) post epost =
    wp (MonadStateOf.modifyGet f : StateT σ m α) post epost := by
  rfl

@[simp]
theorem get_MonadState_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] [MonadStateOf σ m] :
  wp (MonadState.get : m σ) post epost =
    wp (MonadStateOf.get : m σ) post epost := by
  rfl

@[simp]
theorem set_MonadState_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] [MonadStateOf σ m] (x : σ) :
  wp (MonadState.set x : m PUnit) post epost =
    wp (MonadStateOf.set x : m PUnit) post epost := by
  rfl

@[simp]
theorem modifyGet_MonadState_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] [MonadStateOf σ m] (f : σ → α × σ) :
  wp (MonadState.modifyGet f : m α) post epost =
    wp (MonadStateOf.modifyGet f : m α) post epost := by
  rfl

@[simp]
theorem read_MonadReader_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] [MonadReaderOf ρ m] :
  wp (MonadReader.read : m ρ) post epost =
    wp (MonadReaderOf.read : m ρ) post epost := by
  rfl

@[simp]
theorem readThe_ReaderT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] :
  wp (readThe ρ : ReaderT ρ m ρ) post epost =
    wp (MonadReaderOf.read : ReaderT ρ m ρ) post epost := by
  rfl

/-! ## MonadLift simp lemmas -/

@[simp]
theorem monadLift_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : m α) (post : α → σ → l) :
  (fun s => wp x (fun a => post a s) epost) ⊑
    wp (MonadLift.monadLift x : StateT σ m α) post epost := by
  intro s
  simp only [wp, MonadLift.monadLift, StateT.lift]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_bind
  apply WPMonad.wp_cons (m := m); intro a
  simp [WPMonad.wp_pure (m := m), PartialOrder.rel_refl]

@[simp]
theorem monadLift_ReaderT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : m α) :
  wp (MonadLift.monadLift x : ReaderT ρ m α) post epost =
    fun r => wp x (fun a => post a r) epost := by
  rfl

@[simp]
theorem monadLift_ExceptT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : m α) (post : α → l) (epost : e × (ε → l)) :
  wp x post epost.1 ⊑
    wp (MonadLift.monadLift x : ExceptT ε m α) post epost := by
  simp only [wp, MonadLift.monadLift, ExceptT.lift, ExceptT.mk]
  apply PartialOrder.rel_trans; rotate_left
  · exact WPMonad.wp_map (m := m) Except.ok x _ _
  · exact PartialOrder.rel_refl

@[simp]
theorem lift_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : m α) :
  wp (StateT.lift x : StateT σ m α) post epost =
    wp (MonadLift.monadLift x : StateT σ m α) post epost := by
  rfl

@[simp]
theorem lift_ExceptT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : m α) :
  wp (ExceptT.lift x : ExceptT ε m α) post epost =
    wp (MonadLift.monadLift x : ExceptT ε m α) post epost := by
  rfl

@[simp]
theorem monadLift_OptionT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : m α) :
  wp x post epost.1 ⊑
    wp (MonadLift.monadLift x : OptionT m α) post epost := by
  simp only [wp, MonadLift.monadLift, OptionT.mk, OptionT.lift, OptionT.run]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_bind
  apply WPMonad.wp_cons (m := m); intro a
  simp [WPMonad.wp_pure (m := m), PartialOrder.rel_refl]

@[simp]
theorem lift_OptionT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] [WPMonad (OptionT m) l (e × l)] (x : m α) :
  wp (OptionT.lift x : OptionT m α) post epost =
    wp (MonadLift.monadLift x : OptionT m α) post epost := rfl

/-! ## MonadFunctor simp lemmas -/

@[simp]
theorem monadMap_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e]
  (f : ∀{β}, m β → m β) {α} (x : StateT σ m α) (post : α → σ → l) (epost : e) :
  wp (MonadFunctor.monadMap (m:=m) f x : StateT σ m α) post epost =
    fun s => wp (f (x.run s)) (fun (a, s') => post a s') epost := by
  funext s
  simp only [wp, MonadFunctor.monadMap, StateT.run]

@[simp]
theorem monadMap_ReaderT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e]
  (f : ∀{β}, m β → m β) {α} (x : ReaderT ρ m α) (post : α → ρ → l) (epost : e) :
  wp (MonadFunctor.monadMap (m:=m) f x : ReaderT ρ m α) post epost =
    fun r => wp (f (x.run r)) (fun a => post a r) epost := by
  funext r
  simp only [wp, MonadFunctor.monadMap, ReaderT.run]

@[simp]
theorem monadMap_ExceptT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e]
  (f : ∀{β}, m β → m β) {α} (x : ExceptT ε m α) (post : α → l) (epost : e × (ε → l)) :
  wp (MonadFunctor.monadMap (m:=m) f x : ExceptT ε m α) post epost =
    wp (f x.run) (fun r => match r with | .ok a => post a | .error e => epost.2 e) epost.1 := by
  simp only [wp, MonadFunctor.monadMap, ExceptT.run]; rfl

@[simp]
theorem monadMap_OptionT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e]
  (f : ∀{β}, m β → m β) {α} (x : OptionT m α) (post : α → l) (epost : e × l) :
  wp (MonadFunctor.monadMap (m:=m) f x : OptionT m α) post epost =
    wp (f x.run) (fun o => match o with | some a => post a | none => epost.2) epost.1 := by
  simp only [wp, MonadFunctor.monadMap, OptionT.run]; rfl

@[simp]
theorem withReader_ReaderT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (f : ρ → ρ) (x : ReaderT ρ m α) :
  wp (MonadWithReaderOf.withReader f x : ReaderT ρ m α) post epost =
    fun r => wp x (fun a _ => post a r) epost (f r) := rfl

@[simp]
theorem withReader_MonadWithReader_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] [MonadWithReaderOf ρ m] (f : ρ → ρ) (x : m α) :
  wp (MonadWithReader.withReader f x : m α) post epost =
    wp (MonadWithReaderOf.withReader f x : m α) post epost := rfl

@[simp]
theorem withTheReader_ReaderT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (f : ρ → ρ) (x : ReaderT ρ m α) :
  wp (withTheReader ρ f x : ReaderT ρ m α) post epost =
    wp (MonadWithReaderOf.withReader f x : ReaderT ρ m α) post epost := rfl

/-! ## Transformer adapt lemmas -/

@[simp]
theorem adapt_ExceptT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (f : ε → ε') (x : ExceptT ε m α) :
  wp x post (epost.1, fun e => epost.2 (f e)) ⊑
    wp (ExceptT.adapt f x : ExceptT ε' m α) post epost := by
  simp only [wp, ExceptT.adapt, ExceptT.mk]
  apply PartialOrder.rel_trans; rotate_left
  · exact WPMonad.wp_map (m := m) (Except.mapError f) x _ _
  · apply WPMonad.wp_cons (m := m); intro r; cases r <;> exact PartialOrder.rel_refl

@[simp]
theorem adaptExcept_EStateM_wp (f : ε → ε') (x : EStateM ε σ α) :
  wp (EStateM.adaptExcept f x : EStateM ε' σ α) post epost =
    wp x post (fun e => epost (f e)) := by
  funext s
  simp only [wp, EStateM.adaptExcept]
  cases (x s) <;> simp

/-! ## MonadControl simp lemmas -/

@[simp]
theorem liftWith_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e]
  (f : (∀{β}, StateT σ m β → m (β × σ)) → m α) :
  (fun s => wp (f (fun x => x.run s)) (fun a => post a s) epost) ⊑
    wp (MonadControl.liftWith (m:=m) f : StateT σ m α) post epost := by
  simp [MonadControl.liftWith, liftM, get]
  apply PartialOrder.rel_trans; rotate_left
  { apply WPMonad.wp_bind }
  intro s; simp
  apply PartialOrder.rel_trans; rotate_left; apply monadLift_StateT_wp; simp
  apply PartialOrder.rel_refl

@[simp]
theorem liftWith_ReaderT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e]
  (f : (∀{β}, ReaderT ρ m β → m β) → m α) :
  wp (MonadControl.liftWith (m:=m) f : ReaderT ρ m α) post epost =
    fun r => wp (f (fun x => x.run r)) (fun a => post a r) epost := by
  funext r
  simp only [wp, MonadControl.liftWith, ReaderT.run]

@[simp]
theorem liftWith_ExceptT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e]
  (f : (∀{β}, ExceptT ε m β → m (Except ε β)) → m α) :
  wp (f (fun x => x.run)) post epost.1 ⊑
    wp (MonadControl.liftWith (m:=m) f : ExceptT ε m α) post epost := by
  simp only [wp, MonadControl.liftWith, ExceptT.run]
  apply PartialOrder.rel_trans; rotate_left
  · exact WPMonad.wp_map (m := m) Except.ok (f fun {β} => id) _ _
  · exact PartialOrder.rel_refl

@[simp]
theorem liftWith_OptionT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e]
  (f : (∀{β}, OptionT m β → m (Option β)) → m α) :
  wp (f (fun x => x.run)) post epost.1 ⊑
    wp (MonadControl.liftWith (m:=m) f : OptionT m α) post epost := by
  simp [MonadControl.liftWith, liftM, monadLift]

@[simp]
theorem restoreM_StateT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : m (α × σ)) :
  (fun _ => wp x (fun (a, s) => post a s) epost) ⊑
    wp (MonadControl.restoreM (m:=m) x : StateT σ m α) post epost := by
  simp only [MonadControl.restoreM]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_bind; simp only [liftM, monadLift]
  apply PartialOrder.rel_trans; rotate_left; apply monadLift_StateT_wp
  intro s; apply WPMonad.wp_cons; intro s'; simp only
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_bind
  simp [set, StateT.set, pure, StateT.pure]; apply PartialOrder.rel_refl

@[simp]
theorem restoreM_ReaderT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : m α) :
  wp (MonadControl.restoreM (m:=m) x : ReaderT ρ m α) post epost =
    fun r => wp x (fun a => post a r) epost := by
  funext r
  simp only [wp, MonadControl.restoreM]

@[simp]
theorem restoreM_ExceptT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : m (Except ε α)) :
  wp (MonadControl.restoreM (m:=m) x : ExceptT ε m α) post epost =
    wp x (fun r => match r with | .ok a => post a | .error e => epost.2 e) epost.1 := by
  simp only [wp, MonadControl.restoreM]; rfl

@[simp]
theorem restoreM_OptionT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : m (Option α)) :
  wp (MonadControl.restoreM (m:=m) x : OptionT m α) post epost =
    wp x (fun o => match o with | some a => post a | none => epost.2) epost.1 := by
  simp only [wp, MonadControl.restoreM]; rfl

@[simp]
theorem controlAt_wp [Bind n] [Monad n] [Monad m] [CompleteLattice l] [WPMonad n l e] [MonadControlT m n]
  (f : (∀{β}, n β → m (stM m n β)) → m (stM m n α)) :
  wp (controlAt m f : n α) post epost =
    wp (liftWith f >>= restoreM : n α) post epost := by
  rfl

@[simp]
theorem control_wp [Bind n] [Monad n] [Monad m] [CompleteLattice l] [WPMonad n l e] [MonadControlT m n]
  (f : (∀{β}, n β → m (stM m n β)) → m (stM m n α)) :
  wp (control f : n α) post epost =
    wp (liftWith f >>= restoreM : n α) post epost := by
  rfl

@[simp]
theorem monadLift_trans_wp [Monad o] [CompleteLattice l] [WPMonad o l e] [MonadLift n o] [MonadLiftT m n] (x : m α) :
  wp (MonadLiftT.monadLift x : o α) post epost =
    wp (MonadLift.monadLift (m:=n) (MonadLiftT.monadLift (m:=m) x) : o α) post epost := rfl

@[simp]
theorem monadLift_refl_wp [Monad m] [CompleteLattice l] [WPMonad m l e] (x : m α) :
  wp (MonadLiftT.monadLift x : m α) post epost =
    wp (x : m α) post epost := rfl

@[simp]
theorem monadMap_trans_wp [Monad o] [CompleteLattice l] [WPMonad o l e] [MonadFunctor n o] [MonadFunctorT m n] (x : o α) :
  wp (MonadFunctorT.monadMap f x : o α) post epost =
    wp (MonadFunctor.monadMap (m:=n) (MonadFunctorT.monadMap (m:=m) f) x : o α) post epost := by rfl

@[simp]
theorem monadMap_refl_wp [Monad m] [CompleteLattice l] [WPMonad m l e] (x : m α) :
  wp (MonadFunctorT.monadMap f x : m α) post epost =
    wp (f x : m α) post epost := by rfl


@[simp]
theorem get_MonadStateOf_lift_wp [MonadStateOf σ m] [MonadLift m n] [Monad m] [Monad n] [CompleteLattice l] [WPMonad n l e'] :
  wp (MonadStateOf.get : n σ) post epost =
    wp (MonadLift.monadLift (MonadStateOf.get : m σ) : n σ) post epost := by
  rfl

@[simp]
theorem set_MonadStateOf_lift_wp [MonadStateOf σ m] [MonadLift m n] [Monad m] [Monad n] [CompleteLattice l] [WPMonad n l e'] (x : σ) :
  wp (MonadStateOf.set x : n PUnit) post epost =
    wp (MonadLift.monadLift (MonadStateOf.set (σ:=σ) x : m PUnit) : n PUnit) post epost := by
  rfl

@[simp]
theorem modifyGet_MonadStateOf_lift_wp [MonadStateOf σ m] [MonadLift m n] [Monad m] [Monad n] [CompleteLattice l] [WPMonad n l e']
  (f : σ → α × σ) :
  wp (MonadStateOf.modifyGet f : n α) post epost =
    wp (MonadLift.monadLift (MonadState.modifyGet f : m α) : n α) post epost := by
  rfl

@[simp]
theorem read_MonadReaderOf_lift_wp [MonadReaderOf ρ m] [MonadLift m n] [Monad m] [Monad n] [CompleteLattice l] [WPMonad n l e'] :
  wp (MonadReaderOf.read : n ρ) post epost =
    wp (MonadLift.monadLift (MonadReader.read : m ρ) : n ρ) post epost := by
  rfl

@[simp]
theorem throw_lift_ExceptT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e'] [MonadExceptOf ε m] (err : ε) :
  wp (MonadExceptOf.throw (ε:=ε) err : ExceptT ε' m α) post epost =
    wp (MonadExceptOf.throw (ε:=ε) err : m (Except ε' α)) (fun r => match r with | .ok a => post a | .error e => epost.2 e) epost.1 := by
  rfl

@[simp]
theorem throw_lift_OptionT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e'] [MonadExceptOf ε m] (err : ε) :
  wp (MonadExceptOf.throw (ε:=ε) err : OptionT m α) post epost =
    wp (MonadExceptOf.throw (ε:=ε) err : m (Option α)) (fun o => match o with | some a => post a | none => epost.2) epost.1 := by
  rfl

@[simp]
theorem tryCatch_lift_ExceptT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e'] [MonadExceptOf ε m] (x : ExceptT ε' m α) (h : ε → ExceptT ε' m α) :
  wp (MonadExceptOf.tryCatch (ε:=ε) x h : ExceptT ε' m α) post epost =
    wp (MonadExceptOf.tryCatch (ε:=ε) x h : m (Except ε' α)) (fun r => match r with | .ok a => post a | .error e => epost.2 e) epost.1 := by
  rfl

@[simp]
theorem tryCatch_lift_OptionT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e'] [MonadExceptOf ε m] (x : OptionT m α) (h : ε → OptionT m α) :
  wp (MonadExceptOf.tryCatch (ε:=ε) x h : OptionT m α) post epost =
    wp (MonadExceptOf.tryCatch (ε:=ε) x h : m (Option α)) (fun o => match o with | some a => post a | none => epost.2) epost.1 := by
  rfl

@[simp]
theorem throw_ReaderT_lift_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e'] [MonadExceptOf ε m] (err : ε) :
  wp (MonadExceptOf.throw (ε:=ε) err : ReaderT ρ m α) post epost =
    wp (MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) err : m α) : ReaderT ρ m α) post epost := by
  rfl

@[simp]
theorem throw_StateT_lift_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e'] [MonadExceptOf ε m] (err : ε) :
  wp (MonadExceptOf.throw (ε:=ε) err : StateT σ m α) post epost =
    wp (MonadLift.monadLift (MonadExceptOf.throw (ε:=ε) err : m α) : StateT σ m α) post epost := by
  rfl

@[simp]
theorem tryCatch_ReaderT_lift_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e'] [MonadExceptOf ε m] (x : ReaderT ρ m α) (h : ε → ReaderT ρ m α) :
  wp (MonadExceptOf.tryCatch (ε:=ε) x h : ReaderT ρ m α) post epost =
    fun r => wp (MonadExceptOf.tryCatch (ε:=ε) (x.run r) (fun e => (h e).run r) : m α) (fun a => post a r) epost := by
  rfl

@[simp]
theorem tryCatch_StateT_lift_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e'] [MonadExceptOf ε m] (x : StateT σ m α) (h : ε → StateT σ m α) :
  wp (MonadExceptOf.tryCatch (ε:=ε) x h : StateT σ m α) post epost =
    fun s => wp (MonadExceptOf.tryCatch (ε:=ε) (x.run s) (fun e => (h e).run s) : m (α × σ)) (fun (a, s') => post a s') epost := by
  rfl

@[simp]
theorem liftWith_trans_wp [Monad o] [CompleteLattice l] [WPMonad o l e] [MonadControl n o] [MonadControlT m n]
  (f : (∀{β}, o β → m (stM m o β)) → m α) :
  wp (MonadControlT.liftWith f : o α) post epost =
    wp (MonadControl.liftWith (m:=n) fun x₂ => MonadControlT.liftWith fun x₁ => f (x₁ ∘ x₂) : o α) post epost := by
  rfl

@[simp]
theorem liftWith_refl_wp [Pure m] [Monad m] [CompleteLattice l] [WPMonad m l e]
  (f : (∀{β}, m β → m β) → m α) :
  wp (MonadControlT.liftWith (m:=m) f : m α) post epost =
    wp (f (fun x => x) : m α) post epost := by
  rfl

@[simp]
theorem restoreM_trans_wp [Monad o] [CompleteLattice l] [WPMonad o l e] [MonadControl n o] [MonadControlT m n] (x : stM m o α) :
  wp (MonadControlT.restoreM x : o α) post epost =
    wp (MonadControl.restoreM (m:=n) (MonadControlT.restoreM (m:=m) x) : o α) post epost := by
  rfl

@[simp]
theorem restoreM_refl_wp [Pure m] [Monad m] [CompleteLattice l] [WPMonad m l e] (x : stM m m α) :
  wp (MonadControlT.restoreM x : m α) post epost =
    wp (Pure.pure x : m α) post epost := by
  rfl

/-! ## OrElse simp lemmas -/

@[simp]
theorem orElse_Except_wp (x : Except ε α) (h : Unit → Except ε α) :
  wp (OrElse.orElse x h : Except ε α) post epost =
    wp x post (fun _ => wp (h ()) post epost) := by
  simp only [wp, OrElse.orElse, MonadExcept.orElse]
  cases x <;> rfl

@[simp]
theorem orElse_ExceptT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : ExceptT ε m α) (h : Unit → ExceptT ε m α) :
  wp x post (epost.1, fun _ => wp (h ()) post epost) ⊑
    wp (OrElse.orElse x h : ExceptT ε m α) post epost := by
  simp only [wp, OrElse.orElse, MonadExcept.orElse]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_bind
  apply WPMonad.wp_cons (m := m); intro r; cases r <;> simp [PartialOrder.rel_refl]

@[simp]
theorem orElse_Option_wp (x : Option α) (h : Unit → Option α) :
  ∀ post (epost : Prop),
  wp (OrElse.orElse x h : Option α) post epost =
    wp x post (wp (h ()) post epost) := by
  simp only [wp, OrElse.orElse, Option.orElse]
  cases x <;> simp

@[simp]
theorem orElse_EStateM_wp (x : EStateM ε σ α) (h : Unit → EStateM ε σ α) :
  wp (OrElse.orElse x h : EStateM ε σ α) post epost =
    fun s => wp x post (fun _ s' => wp (h ()) post epost s') s := by
  funext s
  simp only [wp, OrElse.orElse, EStateM.orElse]
  cases x s <;> simp; rfl

@[simp]
theorem orElse_OptionT_wp [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (x : OptionT m α) (h : Unit → OptionT m α) :
  wp x post (epost.1, wp (h ()) post epost) ⊑
    wp (OrElse.orElse x h : OptionT m α) post epost := by
  simp only [wp, OrElse.orElse, OptionT.run]
  apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_bind
  apply WPMonad.wp_cons (m := m); intro o; cases o with
  | some a => simp [WPMonad.wp_pure (m := m), PartialOrder.rel_refl]
  | none => exact PartialOrder.rel_refl

end Loom.WP
