open Lean.Order

universe u

inductive EPost : List (Type u) -> Type _ where
  | nil : EPost []
  | cons {es : List (Type u)} {e : Type u} (epost : e) : EPost es -> EPost (e :: es)

syntax "EPost⟨" term,* "⟩" : term

macro_rules
  | `(EPost⟨$tps,*⟩) => `(EPost.cons [$tps,*])

@[app_unexpander EPost] meta def unexpandEPostNil : Lean.PrettyPrinter.Unexpander
  | `($(_) [$es:term,*] ) => `(EPost⟨$es,*⟩)
  | _ => throw ()

/--
`post⟨e₁, e₂, ..., eₙ⟩` builds an `EPost` list.
Each element type is inferred via `EPost.cons _ eᵢ ...`.
-/
syntax "epost⟨" term,* "⟩" : term

macro_rules
  | `(epost⟨⟩) => `(EPost.nil)
  | `(epost⟨$x⟩) => `(EPost.cons $x EPost.nil)
  | `(epost⟨$x, $xs,*⟩) => `(EPost.cons $x epost⟨$xs,*⟩)

@[app_unexpander EPost.nil] meta def unexpandEpostNil : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `(epost⟨⟩)

@[app_unexpander EPost.cons] meta def unexpandEpostCons : Lean.PrettyPrinter.Unexpander
  | `($(_) $x $tail) =>
    match tail with
    | `(epost⟨⟩) => `(epost⟨$x⟩)
    | `(epost⟨$y⟩) => `(epost⟨$x, $y⟩)
    | `(epost⟨$y, $ys,*⟩) => `(epost⟨$x, $y, $ys,*⟩)
    | _ => throw ()
  | _ => throw ()

-- #check epost⟨1, true⟩

def EPost.head : EPost (e :: es) → e
  | .cons epost _ => epost

def EPost.tail : EPost (e :: es) → EPost es
  | .cons _ epost => epost
