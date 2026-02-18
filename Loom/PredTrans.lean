import Loom.LatticeExt

open Lean.Order

/-!
# Predicate Transformer

The predicate transformer type for weakest precondition semantics.

`PredTrans l e α` wraps a function `(α → l) → e → l` that transforms a postcondition
`post : α → l` and exception continuation `epost : e` into a precondition of type `l`.

The structure projection `trans` is not used directly.
Instead, `PredTrans.apply` is provided as the API, with `@[simp]` lemmas that reduce
applications of monadic combinators through `apply`.
-/

/-! ## Monotonicity -/

/-- A predicate transformer is monotone if stronger postconditions yield stronger preconditions. -/
def PredTrans.Monotone {l : Type v} {e : Type w} {α : Type u} [PartialOrder l] [PartialOrder e] (trans : (α → l) → e → l) :=
  ∀ (post₁ post₂ : α → l) (epost₁ epost₂ : e) (hpost : ∀ a, post₁ a ⊑ post₂ a) (hepost : epost₁ ⊑ epost₂),
    trans post₁ epost₁ ⊑ trans post₂ epost₂

/--
The type of predicate transformers for weakest precondition semantics.

A predicate transformer `wp : PredTrans l e α` takes a postcondition `post : α → l` and
exception continuation `epost : e` and returns a precondition `wp.apply post epost : l`.
-/
structure PredTrans (l : Type v) (e : Type w) [PartialOrder l] [PartialOrder e] (α : Type u) where
  /-- The underlying function of the predicate transformer. -/
  trans : (α → l) → e → l
  /-- The predicate transformer is monotone in both postcondition and exception continuation. -/
  mono : PredTrans.Monotone trans

namespace PredTrans

/-! ## Core API -/

variable {l : Type v} {e : Type w} [PartialOrder l] [PartialOrder e]

/-- Apply the predicate transformer to a postcondition and exception continuation. -/
def apply (pt : PredTrans l e α) (post : α → l) (epost : e) : l := pt.trans post epost

@[ext]
theorem ext {trans₁ trans₂ : PredTrans l e α}
    (h : ∀ post epost, trans₁.apply post epost = trans₂.apply post epost) : trans₁ = trans₂ := by
  obtain ⟨t1, m1⟩ := trans₁; obtain ⟨t2, m2⟩ := trans₂
  have : t1 = t2 := funext fun post => funext fun epost => h post epost
  subst this; rfl

@[simp]
theorem apply_mk (f : (α → l) → e → l) (hmono : PredTrans.Monotone f) (post : α → l) (epost : e) :
    (PredTrans.mk f hmono).apply post epost = f post epost := rfl

instance : CoeFun (PredTrans l e α) (fun _ => (α → l) → e → l) :=
  ⟨fun wp => wp.apply⟩

/-! ## Monad instance -/

instance instMonad : Monad (PredTrans l e) where
  pure x := ⟨fun post _epost => post x, fun _ _ _ _ hpost _ => hpost x⟩
  bind x f := ⟨fun post epost => x.trans (fun a => (f a).trans post epost) epost, by
    intro p1 p2 e1 e2 hp he
    apply x.mono
    · intro a; exact (f a).mono p1 p2 e1 e2 hp he
    · exact he⟩

instance instLawfulMonad : LawfulMonad (PredTrans l e) where
  map_const := rfl
  id_map _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := rfl

/-! ## MonadExcept instance -/

instance instMonadExceptOf : MonadExceptOf ε (PredTrans l (e × (ε → l))) where
  throw err := ⟨fun _post epost => epost.2 err, fun _ _ _ _ _ hepost => hepost.2 err⟩
  tryCatch x handle := ⟨fun post epost => x.trans post (epost.1, fun e => (handle e).trans post epost), by
    intro p1 p2 e1 e2 hp he
    apply x.mono
    · exact hp
    · exact ⟨he.1, fun err => (handle err).mono p1 p2 e1 e2 hp he⟩⟩

/-! ## Simp lemmas for `apply` -/

@[simp, grind =]
theorem apply_pure (a : α) (post : α → l) (epost : e) :
    (pure a : PredTrans l e α).apply post epost = post a := rfl

@[simp, grind =]
theorem apply_bind (x : PredTrans l e α) (f : α → PredTrans l e β) (post : β → l) (epost : e) :
    (x >>= f).apply post epost = x.apply (fun a => (f a).apply post epost) epost := rfl

@[simp, grind =]
theorem apply_map (x : PredTrans l e α) (f : α → β) (post : β → l) (epost : e) :
    (f <$> x).apply post epost = x.apply (fun a => post (f a)) epost := rfl

@[simp]
theorem apply_seq (f : PredTrans l e (α → β)) (x : PredTrans l e α) (post : β → l) (epost : e) :
    (f <*> x).apply post epost = f.apply (fun g => x.apply (fun a => post (g a)) epost) epost := rfl

@[simp]
theorem apply_seqLeft (x : PredTrans l e α) (y : PredTrans l e β) (post : α → l) (epost : e) :
    (x <* y).apply post epost = x.apply (fun a => y.apply (fun _ => post a) epost) epost := rfl

@[simp]
theorem apply_seqRight (x : PredTrans l e α) (y : PredTrans l e β) (post : β → l) (epost : e) :
    (x *> y).apply post epost = x.apply (fun _ => y.apply post epost) epost := rfl

@[simp, grind =]
theorem apply_throw (err : ε) (post : α → l) (epost : e × (ε → l)) :
    (throw err : PredTrans l (e × (ε → l)) α).apply post epost = epost.2 err := rfl

@[simp, grind =]
theorem apply_tryCatch (x : PredTrans l (e × (ε → l)) α) (h : ε → PredTrans l (e × (ε → l)) α) (post : α → l) (epost : e × (ε → l)) :
    (tryCatch x h).apply post epost = x.apply post (epost.1, fun err => (h err).apply post epost) := rfl

@[simp]
theorem apply_dite (c : Prop) [Decidable c] (tthen : c → PredTrans l e α) (telse : ¬c → PredTrans l e α)
    (post : α → l) (epost : e) :
    (if h : c then tthen h else telse h).apply post epost =
      if h : c then (tthen h).apply post epost else (telse h).apply post epost := by
  split <;> rfl

@[simp]
theorem apply_ite (c : Prop) [Decidable c] (tthen telse : PredTrans l e α) (post : α → l) (epost : e) :
    (if c then tthen else telse).apply post epost =
      if c then tthen.apply post epost else telse.apply post epost := by
  split <;> rfl

/-! ## `pushExcept` -/

/-- The `Except`-decomposing postcondition for `pushExcept`. -/
abbrev pushExcept.post {l : Type u} (post : α → l) (epost : (ε → l) × e) : Except ε α → l :=
  fun | .ok a => post a | .error e => epost.1 e

/--
Adds the ability to make assertions about exceptions of type `ε` to a predicate transformer with
exception type `e`, resulting in exception type `e × (ε → l)`. This is done by
interpreting `Except ε`-valued predicate transformers.

This can be used for all kinds of exception-like effects, such as early termination, by interpreting
them as exceptions.
-/
def pushExcept (x : PredTrans l e (Except ε α)) : PredTrans l ((ε → l) × e) α :=
  ⟨fun post epost => x.trans (pushExcept.post post epost) epost.2, by
    intro p1 p2 e1 e2 hp he
    apply x.mono
    · intro r; cases r with
      | ok a => exact hp a
      | error err => exact he.1 err
    · exact he.2⟩

@[simp, grind =]
theorem apply_pushExcept (x : PredTrans l e (Except ε α)) (post : α → l) (epost : (ε → l) × e) :
    (pushExcept x).apply post epost =
      x.apply (pushExcept.post post epost) epost.2 := rfl

/-! ## `pushArg` -/

/--
Adds the ability to make assertions about a state of type `σ` to a predicate transformer,
resulting in a predicate transformer with precondition type `σ → l`. This is done by
interpreting state-passing-style predicate transformers.

This can be used for all kinds of state-like effects, including reader effects or append-only
states, by interpreting them as states.
-/
def pushArg {σ : Type u} (x : σ → PredTrans l e (α × σ)) : PredTrans (σ → l) e α :=
  ⟨fun post epost s => (x s).trans (fun (a, s) => post a s) epost, by
    intro p1 p2 e1 e2 hp he s
    apply (x s).mono
    · intro ⟨a, s'⟩; exact hp a s'
    · exact he⟩

@[simp, grind =]
theorem apply_pushArg {σ : Type u} (x : σ → PredTrans l e (α × σ))
    (post : α → σ → l) (epost : e) (s : σ) :
    (pushArg x).apply post epost s = (x s).apply (fun (a, s) => post a s) epost := rfl

end PredTrans
