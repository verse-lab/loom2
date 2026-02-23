import Lean
import Loom.Test.Driver
import Loom.Tactic.VCGen

open Loom Lean Meta Order

abbrev M := ExceptT String <| StateM Nat

@[lspec] theorem spec_throw (e : String) {post : α → Nat → Prop} {epost : EPost⟨String → Nat → Prop⟩} :
    epost.1 e ⊑ wp (throw (m := M) e) post epost := PartialOrder.rel_refl

@[lspec] theorem spec_set (x : Nat) {post : PUnit → Nat → Prop} {epost : EPost⟨String → Nat → Prop⟩} :
    (fun _ => post ⟨⟩ x) ⊑ wp (set (m := M) x) post epost := PartialOrder.rel_refl

@[lspec] theorem spec_get (post : Nat → Nat → Prop) {epost : EPost⟨String → Nat → Prop⟩} :
    (fun s => post s s) ⊑ wp (get (m := M)) post epost := PartialOrder.rel_refl

@[lspec] theorem spec_pure {m : Type u → Type v} {l e : Type u}
    [Monad m] [CompleteLattice l] [CompleteLattice e] [WPMonad m l e]
    {α : Type u} (a : α) (post : α → l) (epost : e) :
    post a ⊑ wp (pure (f := m) a) post epost := by
  exact WPMonad.wp_pure a post epost

@[lspec] theorem spec_bind {m : Type u → Type v} {l e : Type u}
    [Monad m] [CompleteLattice l] [CompleteLattice e] [WPMonad m l e]
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

-- example : Goal 10 := by
--   intro post epost h
--   mvcgen'
--   all_goals sorry

#eval
  runBenchUsingTactic
    ``Goal [``loop, ``step]
    `(tactic| (intro post epost h; mvcgen'))
    `(tactic| sorry)
    [1000]
