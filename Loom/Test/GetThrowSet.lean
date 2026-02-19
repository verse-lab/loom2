import Lean
import Loom.Test.Driver
import Loom.Tactic.VCGen

open Loom Lean Meta Order

@[lspec] theorem spec_get_StateT' {m : Type u → Type v} {l e : Type u}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e]
    {σ : Type u} (post : σ → σ → l) (epost : e) :
    (fun s => post s s) ⊑ wp (get : StateT σ m σ) post epost :=
  WP.get_StateT_wp post epost

@[lspec] theorem spec_set_StateT' {m : Type u → Type v} {l e : Type u}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e]
    {σ : Type u} (x : σ) (post : PUnit → σ → l) (epost : e) :
    (fun _ => post ⟨⟩ x) ⊑ wp (set x : StateT σ m PUnit) post epost := by
  exact WP.set_StateT_wp x post epost

@[lspec] theorem spec_monadLift_ExceptT {m : Type u → Type v} {l e : Type u}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e]
    {ε α : Type u} (x : m α) (post : α → l) (epost : (ε → l) × e) :
    wp x post epost.2 ⊑ wp (MonadLift.monadLift x : ExceptT ε m α) post epost := by
  exact WP.monadLift_ExceptT_wp x post epost

@[lspec] theorem spec_MonadStateOf_get_ExceptT {m : Type u → Type v} {l e : Type u}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e]
    [MonadStateOf σ m] (post : σ → l) (epost : (ε → l) × e) :
    wp (MonadLift.monadLift (MonadStateOf.get : m σ) : ExceptT ε m σ) post epost ⊑
      wp (MonadStateOf.get : ExceptT ε m σ) post epost := by
  rfl

@[lspec] theorem spec_MonadStateOf_set_ExceptT {m : Type u → Type v} {l e : Type u}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e]
    [MonadStateOf σ m] (x : σ) (post : PUnit → l) (epost : (ε → l) × e) :
    wp (MonadLift.monadLift (MonadStateOf.set (σ := σ) x : m PUnit) : ExceptT ε m PUnit) post epost ⊑
      wp (MonadStateOf.set (σ := σ) x : ExceptT ε m PUnit) post epost := by
  rfl

@[lspec] theorem spec_get_ExceptT {m : Type u → Type v} {l e : Type u}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e]
    [MonadStateOf σ m] (post : σ → l) (epost : (ε → l) × e) :
    wp (MonadLift.monadLift (get (m := m) : m σ) : ExceptT ε m σ) post epost ⊑
      wp (get (m := ExceptT ε m) : ExceptT ε m σ) post epost := by
  rfl

@[lspec] theorem spec_set_ExceptT {m : Type u → Type v} {l e : Type u}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e]
    [MonadStateOf σ m] (x : σ) (post : PUnit → l) (epost : (ε → l) × e) :
    wp (MonadLift.monadLift (set (m := m) x : m PUnit) : ExceptT ε m PUnit) post epost ⊑
      wp (set (m := ExceptT ε m) x : ExceptT ε m PUnit) post epost := by
  rfl

@[lspec] theorem spec_throw_ExceptT {m : Type u → Type v} {l e : Type u}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e]
    {ε α : Type u} (err : ε) (post : α → l) (epost : (ε → l) × e) :
    epost.1 err ⊑ wp (MonadExceptOf.throw err : ExceptT ε m α) post epost := by
  exact WP.throw_ExceptT_wp err

@[lspec] theorem spec_pure {m : Type u → Type v} {l e : Type u}
    [Monad m] [CompleteLattice l] [WPMonad m l e]
    {α : Type u} (a : α) (post : α → l) (epost : e) :
    post a ⊑ wp (pure (f := m) a) post epost := by
  exact WPMonad.wp_pure a post epost

@[lspec] theorem spec_bind {m : Type u → Type v} {l e : Type u}
    [Monad m] [CompleteLattice l] [WPMonad m l e]
    {α β : Type u} (x : m α) (f : α → m β) (post : β → l) (epost : e) :
    wp x (fun a => wp (f a) post epost) epost ⊑ wp (x >>= f) post epost :=
  WPMonad.wp_bind x f post epost

def step (lim : Nat) : ExceptT String (StateM Nat) Unit := do
  let s ← get
  if s > lim then
    throw "s is too large"
  set (s + 1)

def loop (n : Nat) : ExceptT String (StateM Nat) Unit := do
  match n with
  | 0 => pure ()
  | n+1 => loop n; step n

def Goal (n : Nat) : Prop := ∀ post epost, post n → wp (loop n) (fun _ => post) epost 0

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

-- example : Goal 20 := by
--   intro post epost h
--   mvcgen'
--   all_goals sorry

#eval
  runBenchUsingTactic
    ``Goal [``loop, ``step]
    `(tactic| (intro post epost h; mvcgen'))
    `(tactic| sorry)
    [1000]
