import Lean
import Loom.Test.Driver
import Loom.Tactic.VCGen

open Loom Lean Meta Order

-- Specs for the standalone `get`/`set` functions (which elaborate to MonadState.get/set,
-- a different head constant from MonadStateOf.get/set used above).
@[lspec] theorem spec_get_StateT' {m : Type u → Type v} {l e : Type u}
    [Monad m] [LawfulMonad m] [WPMonad m l e]
    {σ : Type u} (post : σ → σ → l) (epost : e) :
    (fun s => post s s) ⊑ wp (get : StateT σ m σ) post epost :=
  spec_get_StateT post epost

@[lspec] theorem spec_set_StateT' {m : Type u → Type v} {l e : Type u}
    [Monad m] [LawfulMonad m] [WPMonad m l e]
    {σ : Type u} (x : σ) (post : PUnit → σ → l) (epost : e) :
    (fun _ => post ⟨⟩ x) ⊑ wp (set x : StateT σ m PUnit) post epost := sorry
  -- spec_set_StateT x post epost

@[lspec] theorem spec_pure {m : Type u → Type v} {l e : Type u}
    [Monad m] [WPMonad m l e]
    {α : Type u} (a : α) (post : α → l) (epost : e) :
    post a ⊑ wp (pure (f := m) a) post epost := by
  exact WPMonad.wp_pure a post epost

@[lspec] theorem spec_bind {m : Type u → Type v} {l e : Type u}
    [Monad m] [WPMonad m l e]
    {α β : Type u} (x : m α) (f : α → m β) (post : β → l) (epost : e) :
    wp x (fun a => wp (f a) post epost) epost ⊑ wp (x >>= f) post epost :=
  WPMonad.wp_bind x f post epost

def step (v : Nat) : StateM Nat Unit := do
  let s ← get
  set (s + v)
  let s ← get
  set (s - v)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ s post (_ : post s), wp (loop n) (fun _ => post) ⟨⟩ s

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

#eval
  runBenchUsingTactic
    ``Goal [``loop, ``step]
    `(tactic| (intro s post h; mvcgen'))
    `(tactic| grind)
    [1000]
