import Lean
import Loom.Test.Driver
import Loom.Triple.SpecLemmas
import Loom.Test.Specs
import Loom.Tactic.VCGen

open Loom Lean Meta Order

-- Specs for the standalone `get`/`set` functions (which elaborate to MonadState.get/set,
-- a different head constant from MonadStateOf.get/set used above).
@[lspec high] theorem spec_get_StateT' {m : Type u → Type v} {l e : Type u}
    [Monad m] [WPMonad m l e]
    {σ : Type u} (post : σ → σ → l) (epost : e) :
    Triple (fun s => post s s) (get : StateT σ m σ) post epost :=
  by simpa using (spec_get_StateT (m := m) (l := l) (e := e) (σ := σ) post epost)

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

-- set_option trace.Loom.Tactic.vcgen true

def runTests := runBenchUsingTactic
    ``Goal [``loop, ``step]
    `(tactic| (intro s post h; mvcgen'))
    `(tactic| grind)

#eval
  runBenchUsingTactic
    ``Goal [``loop, ``step]
    `(tactic| (intro s post h; mvcgen'))
    `(tactic| grind)
    [1000]
