/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean
import Loom.Tactic.VCGen
import Loom.Test.Driver
import Loom.Lawful.State
import Loom.Lawful.Except

open Lean Parser Meta Elab Tactic Sym Loom Lean.Order

/-!
Same benchmark as `vcgen_add_sub_cancel` but using a deep transformer stack.
-/

abbrev M := ExceptT String <| ReaderT String <| ExceptT Nat <| StateT Nat <| ExceptT Unit <| StateM Unit

/-
Known issues:
* Using `StateT String` instead of `ReaderT String` picks the wrong spec for `MonadStateOf.get`; namely that on `String`.
  It seems we need to disambiguate discrimination tree lookup results with defeq.
* Even using `ReaderT String` it doesn't work. TODO: Why?
* But just using `ExceptT String` works.
-/

def step (v : Nat) : M Unit := do
  let s ← getThe Nat
  set (s + v)
  let s ← getThe Nat
  set (s - v)

def loop (n : Nat) : M Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ post epost s₁ s₂, post s₁ s₂ ⟨⟩ -> wp (loop n) (fun _ => post) epost s₁ s₂ ⟨⟩

@[lspec]
theorem Spec.M_getThe_Nat :
  (fun s₁ s₂ => post s₂ s₁ s₂) ⊑ wp (getThe (m := M) Nat) post epost := by
  apply PartialOrder.rel_trans; rotate_left; apply LawfulMonadStateOf.wp_get
  simp [get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift]
  rfl

@[lspec]
theorem Spec.M_set_Nat (n : Nat) :
  (fun s₁ _ => post ⟨⟩ s₁ n) ⊑ wp (set (m := M) n) post epost := by
  apply PartialOrder.rel_trans; rotate_left; apply LawfulMonadStateOf.wp_set
  simp [set, MonadStateOf.set, liftM, monadLift, MonadLift.monadLift]
  rfl

theorem Spec.M_tryCatchThe (post : α → String → Nat → Unit → Prop) :
  (fun s => wp x post ⟨epost.1, ⟨fun x => wp (h x) post epost s, epost.2.2⟩⟩ s)
  ⊑ wp (tryCatchThe Nat x h : M α) post epost := by
  apply PartialOrder.rel_trans; rotate_left; apply LawfulMonadExceptOf.wp_tryCatch
  simp [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, -ExceptT.apply_wp]
  rfl

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

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

#eval runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| (intro post epost s₁ s₂ h; mvcgen')) `(tactic| grind)
  [1000]
