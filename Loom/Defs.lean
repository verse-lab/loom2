import Loom.ECont

open Lean.Order


variable (m : Type v → Type u)

class WPMonad [Monad m] (l : outParam (Type v)) (ε : outParam (Type v)) [CompleteLattice l] where
  wp : m α → ECont l ε α
  wp_pure (x : α) (post : α → l) (epost : ε → l) : wp (pure (f := m) x) post epost = post x
  wp_bind (x : m α) (f : α → m β) (post : β → l) (epost : ε → l) : wp x (fun x => wp (f x) post epost) epost ⊑ wp (x >>= f) post epost
  wp_cons (x : m α) (post post' : α → l) (epost : ε → l) (h : post ⊑ post') : wp x post epost ⊑ wp x post' epost
  -- wp_econs (x : m α) (post : α → l) (epost epost' : ε → l) (h : epost ⊑ epost') : wp x post epost ⊑ wp x post epost'
