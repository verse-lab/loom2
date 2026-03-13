import Loom.LatticeExt

open Lean.Order

universe u

/- Bundling things together seems to make things too complicated for no reason.
  What should be a notation for PredTrans α l EPost⟨e₁, e₂⟩?
  Post⟨α, l, EPost⟨e₁, e₂⟩⟩?
  or
  Post⟨α → l, EPost⟨e₁, e₂⟩⟩?
  or
  Post⟨α → l, e₁, e₂⟩?

  Seems like this will only confure users
   -/
-- inductive Post (l : Type u) (e : Type w) (α : Type v) where
--   | mk (val : α → l) (exc : e) : Post l e α

-- def Post.val : Post l e α → α → l
--   | .mk val _ => val

-- def Post.exc : Post l e α → e
--   | .mk _ exc => exc

inductive EPost.nil : Type where | mk

inductive EPost.cons (eh : Type u) (et : Type v) where
  | mk : eh -> et -> EPost.cons eh et

@[simp]
def EPost.cons.head : EPost.cons eh et → eh
  | .mk head _ => head

@[simp]
def EPost.cons.tail : EPost.cons eh et → et
  | .mk _ tail => tail

instance : PartialOrder EPost.nil where
  rel _ _ := True
  rel_refl := trivial
  rel_trans _ _ := trivial
  rel_antisymm := fun {p q} _ _ => by cases p; cases q; rfl

instance : CompleteLattice EPost.nil where
  has_sup _ := ⟨EPost.nil.mk, fun _ => ⟨fun _ _ _ => trivial, fun _ => trivial⟩⟩

instance [PartialOrder eh] [PartialOrder et] : PartialOrder (EPost.cons eh et) where
  rel p q := (p.head ⊑ q.head) ⊓ (p.tail ⊑ q.tail)
  rel_refl := by
    intro p
    have h : p.head ⊑ p.head ∧ p.tail ⊑ p.tail := by
      exact And.intro PartialOrder.rel_refl PartialOrder.rel_refl
    simpa [meet_prop_eq_and] using h
  rel_trans := by
    intro p q r h1 h2
    have h1' : p.head ⊑ q.head ∧ p.tail ⊑ q.tail := by
      simpa [meet_prop_eq_and] using h1
    have h2' : q.head ⊑ r.head ∧ q.tail ⊑ r.tail := by
      simpa [meet_prop_eq_and] using h2
    have h : p.head ⊑ r.head ∧ p.tail ⊑ r.tail := by
      exact And.intro
        (PartialOrder.rel_trans h1'.1 h2'.1)
        (PartialOrder.rel_trans h1'.2 h2'.2)
    simpa [meet_prop_eq_and] using h
  rel_antisymm := by
    intro p q h1 h2
    have h1' : p.head ⊑ q.head ∧ p.tail ⊑ q.tail := by
      simpa [meet_prop_eq_and] using h1
    have h2' : q.head ⊑ p.head ∧ q.tail ⊑ p.tail := by
      simpa [meet_prop_eq_and] using h2
    cases p; cases q; congr 1
    · exact PartialOrder.rel_antisymm h1'.1 h2'.1
    · exact PartialOrder.rel_antisymm h1'.2 h2'.2

instance [CompleteLattice eh] [CompleteLattice et] : CompleteLattice (EPost.cons eh et) where
  has_sup c := by
    let supHead : eh := CompleteLattice.sup (fun x => ∃ p, c p ∧ p.head = x)
    let supTail : et := CompleteLattice.sup (fun x => ∃ p, c p ∧ p.tail = x)
    refine ⟨EPost.cons.mk supHead supTail, ?_⟩
    intro q; constructor
    · intro hq p hp
      have hq' : supHead ⊑ q.head ∧ supTail ⊑ q.tail := by
        have hqMeet : (supHead ⊑ q.head) ⊓ (supTail ⊑ q.tail) := by
          simpa [PartialOrder.rel] using hq
        simpa [meet_prop_eq_and] using hqMeet
      have hpq : p.head ⊑ q.head ∧ p.tail ⊑ q.tail := by
        exact And.intro
          (PartialOrder.rel_trans (le_sup _ ⟨p, hp, rfl⟩) hq'.1)
          (PartialOrder.rel_trans (le_sup _ ⟨p, hp, rfl⟩) hq'.2)
      have hpqMeet : (p.head ⊑ q.head) ⊓ (p.tail ⊑ q.tail) := by
        simpa [meet_prop_eq_and] using hpq
      simpa [PartialOrder.rel] using hpqMeet
    · intro h
      have hq : supHead ⊑ q.head ∧ supTail ⊑ q.tail := by
        constructor
        · apply sup_le; rintro _ ⟨p, hp, rfl⟩
          have hpq : p ⊑ q := h p hp
          have hpq' : p.head ⊑ q.head ∧ p.tail ⊑ q.tail := by
            have hpqMeet : (p.head ⊑ q.head) ⊓ (p.tail ⊑ q.tail) := by
              simpa [PartialOrder.rel] using hpq
            simpa [meet_prop_eq_and] using hpqMeet
          exact hpq'.1
        · apply sup_le; rintro _ ⟨p, hp, rfl⟩
          have hpq : p ⊑ q := h p hp
          have hpq' : p.head ⊑ q.head ∧ p.tail ⊑ q.tail := by
            have hpqMeet : (p.head ⊑ q.head) ⊓ (p.tail ⊑ q.tail) := by
              simpa [PartialOrder.rel] using hpq
            simpa [meet_prop_eq_and] using hpqMeet
          exact hpq'.2
      have hqMeet : (supHead ⊑ q.head) ⊓ (supTail ⊑ q.tail) := by
        simpa [meet_prop_eq_and] using hq
      simpa [PartialOrder.rel] using hqMeet

theorem EPost.cons_rel [PartialOrder e] [PartialOrder e'] (eposth : e) (epostt : e') (epost : EPost.cons e e') :
  eposth ⊑ epost.head ->
  epostt ⊑ epost.tail ->
  EPost.cons.mk eposth epostt ⊑ epost := by
  intro hh ht
  simp_all [PartialOrder.rel]

theorem EPost.nil_rel (epost : EPost.nil) :
  EPost.nil.mk ⊑ epost := by
  simp [PartialOrder.rel]

-- instance [PartialOrder l] [PartialOrder e] : PartialOrder (Post l e α) where
--   rel p q := (∀ a, p.val a ⊑ q.val a) ∧ p.exc ⊑ q.exc
--   rel_refl := ⟨fun _ => PartialOrder.rel_refl, PartialOrder.rel_refl⟩
--   rel_trans h1 h2 := ⟨fun a => PartialOrder.rel_trans (h1.1 a) (h2.1 a), PartialOrder.rel_trans h1.2 h2.2⟩
--   rel_antisymm := fun {p q} h1 h2 => by
--     cases p; cases q; congr 1
--     · exact funext fun a => PartialOrder.rel_antisymm (h1.1 a) (h2.1 a)
--     · exact PartialOrder.rel_antisymm h1.2 h2.2

-- instance [CompleteLattice l] [CompleteLattice e] : CompleteLattice (Post l e α) where
--   has_sup c := by
--     refine ⟨Post.mk (fun a => CompleteLattice.sup fun x => ∃ p, c p ∧ p.val a = x)
--                      (CompleteLattice.sup fun x => ∃ p, c p ∧ p.exc = x), ?_⟩
--     intro q; constructor
--     · intro ⟨hv, he⟩ p hp
--       exact ⟨fun a => PartialOrder.rel_trans (le_sup _ ⟨p, hp, rfl⟩) (hv a),
--              PartialOrder.rel_trans (le_sup _ ⟨p, hp, rfl⟩) he⟩
--     · intro h
--       constructor
--       · intro a; apply sup_le; rintro _ ⟨p, hp, rfl⟩; exact (h p hp).1 a
--       · apply sup_le; rintro _ ⟨p, hp, rfl⟩; exact (h p hp).2

syntax "EPost⟨" term,* "⟩" : term
-- syntax "Post⟨" term,+ "⟩" : term
syntax "epost⟨" term,* "⟩" : term
-- syntax "post⟨" term,+ "⟩" : term

macro_rules
  | `(EPost⟨⟩) => `(EPost.nil)
  | `(EPost⟨$x⟩) => `(EPost.cons $x EPost.nil)
  | `(EPost⟨$x, $xs,*⟩) => `(EPost.cons $x EPost⟨$xs,*⟩)
  -- | `(Post⟨$x⟩) => `(Post $x EPost.nil PUnit)
  -- | `(Post⟨$x, $xs,*⟩) => `(Post $x EPost⟨$xs,*⟩ PUnit)
  | `(epost⟨⟩) => `(EPost.nil.mk)
  | `(epost⟨$x⟩) => `(EPost.cons.mk $x EPost.nil.mk)
  | `(epost⟨$x, $xs,*⟩) => `(EPost.cons.mk $x epost⟨$xs,*⟩)
  -- | `(post⟨$x⟩) => `(Post.mk (fun _ : PUnit => $x) EPost.nil.mk)
  -- | `(post⟨$x, $xs,*⟩) => `(Post.mk (fun _ : PUnit => $x) epost⟨$xs,*⟩)

@[app_unexpander EPost.nil] def unexpandEPostNil : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `(EPost⟨⟩)

@[app_unexpander EPost.cons] def unexpandEPostCons : Lean.PrettyPrinter.Unexpander
  | `($(_) $x $xs) =>
    match xs with
    | `(EPost⟨⟩) => `(EPost⟨$x⟩)
    | `(EPost⟨$y⟩) => `(EPost⟨$x, $y⟩)
    | `(EPost⟨$y, $ys,*⟩) => `(EPost⟨$x, $y, $ys,*⟩)
    | _ => `(EPost.cons $x $xs)
  | _ => throw ()

-- @[app_unexpander Post] def unexpandPost : Lean.PrettyPrinter.Unexpander
--   | `($(_) PUnit $x $xs) =>
--     match xs with
--     | `(EPost⟨⟩) => `(Post⟨$x⟩)
--     | `(EPost⟨$y⟩) => `(Post⟨$x, $y⟩)
--     | `(EPost⟨$y, $ys,*⟩) => `(Post⟨$x, $y, $ys,*⟩)
--     | _ => `(Post PUnit $x $xs)
--   | `($(_) $α $x $xs) => `(Post $α $x $xs)
--   | _ => throw ()

@[app_unexpander EPost.nil.mk] def unexpandEPostNilMk : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `(epost⟨⟩)

@[app_unexpander EPost.cons.mk] def unexpandEPostConsMk : Lean.PrettyPrinter.Unexpander
  | `($(_) $x $xs) =>
    match xs with
    | `(epost⟨⟩) => `(epost⟨$x⟩)
    | `(epost⟨$y⟩) => `(epost⟨$x, $y⟩)
    | `(epost⟨$y, $ys,*⟩) => `(epost⟨$x, $y, $ys,*⟩)
    | _ => `(EPost.cons.mk $x $xs)
  | _ => throw ()

-- @[app_unexpander Post.mk] def unexpandPostMk : Lean.PrettyPrinter.Unexpander
--   | `($(_) $post $xs) =>
--     match post with
--     | `(fun $_ => $x) =>
--       match xs with
--       | `(epost⟨⟩) => `(post⟨$x⟩)
--       | `(epost⟨$y⟩) => `(post⟨$x, $y⟩)
--       | `(epost⟨$y, $ys,*⟩) => `(post⟨$x, $y, $ys,*⟩)
--       | _ => `(Post.mk $post $xs)
--     | `(fun $_ : PUnit => $x) =>
--       match xs with
--       | `(epost⟨⟩) => `(post⟨$x⟩)
--       | `(epost⟨$y⟩) => `(post⟨$x, $y⟩)
--       | `(epost⟨$y, $ys,*⟩) => `(post⟨$x, $y, $ys,*⟩)
--       | _ => `(Post.mk $post $xs)
--     | _ => `(Post.mk $post $xs)
--   | _ => throw ()

-- /-- info: Post⟨Nat, Bool⟩ : Type u_1 -/
-- #guard_msgs in
-- #check Post⟨Nat, Bool⟩
/-- info: EPost⟨Nat, Bool, String⟩ : Type -/
#guard_msgs in
#check EPost⟨Nat, Bool, String⟩
-- /-- info: Post⟨Nat, Bool, String⟩ : Type u_1 -/
-- #guard_msgs in
-- #check Post⟨Nat, Bool, String⟩
/-- info: EPost⟨Nat, Bool⟩ : Type -/
#guard_msgs in
#check (EPost.cons Nat (EPost.cons Bool EPost.nil))
-- /-- info: Post⟨Nat, Bool, String⟩ : Type u_1 -/
-- #guard_msgs in
-- #check (Post PUnit Nat (EPost.cons Bool (EPost.cons String EPost.nil)))
/-- info: epost⟨1, true⟩ : EPost⟨Nat, Bool⟩ -/
#guard_msgs in
#check epost⟨1, true⟩
-- /-- info: post⟨1, true⟩ : Post⟨Nat, Bool⟩ -/
-- #guard_msgs in
-- #check post⟨1, true⟩
-- /-- info: post⟨1, true, "x"⟩ : Post⟨Nat, Bool, String⟩ -/
-- #guard_msgs in
-- #check post⟨1, true, "x"⟩

-- Parser/elaborator tests for macro expansions
example : EPost⟨Nat⟩ = EPost.cons Nat EPost.nil := rfl
example : EPost⟨Nat, Bool⟩ = EPost.cons Nat (EPost.cons Bool EPost.nil) := rfl
-- example : Post⟨Nat, Bool⟩ = Post PUnit Nat (EPost.cons Bool EPost.nil) := rfl
-- example : Post⟨Nat, Bool, String⟩ = Post PUnit Nat (EPost.cons Bool (EPost.cons String EPost.nil)) := rfl
example : epost⟨1, true⟩ = EPost.cons.mk 1 (EPost.cons.mk true EPost.nil.mk) := rfl
-- example : post⟨1, true⟩ = Post.mk (fun _ : PUnit => 1) (EPost.cons.mk true EPost.nil.mk) := rfl
-- example : post⟨1, true, "x"⟩ =
  -- Post.mk (fun _ : PUnit => 1) (EPost.cons.mk true (EPost.cons.mk "x" EPost.nil.mk)) := rfl
