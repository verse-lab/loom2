universe u

inductive Post (α : Type v) (l : Type u) (e : Type u) where
  | mk (post : α → l) (epost : e) : Post α l e

def Post.post : Post α l e → α → l
  | .mk post _ => post

def Post.epost : Post α l e → e
  | .mk _ epost => epost

inductive EPost.nil where | mk

inductive EPost.cons (eh et : Type u) where
  | mk : eh -> et -> EPost.cons eh et

def EPost.cons.head : EPost.cons eh et → eh
  | .mk head _ => head

def EPost.cons.tail : EPost.cons eh et → et
  | .mk _ tail => tail

syntax "EPost⟨" term,* "⟩" : term
syntax "Post⟨" term,+ "⟩" : term
syntax "epost⟨" term,* "⟩" : term
syntax "post⟨" term,+ "⟩" : term

macro_rules
  | `(EPost⟨⟩) => `(EPost.nil)
  | `(EPost⟨$x⟩) => `(EPost.cons $x EPost.nil)
  | `(EPost⟨$x, $xs,*⟩) => `(EPost.cons $x EPost⟨$xs,*⟩)
  | `(Post⟨$x⟩) => `(Post PUnit $x EPost.nil)
  | `(Post⟨$x, $xs,*⟩) => `(Post PUnit $x EPost⟨$xs,*⟩)
  | `(epost⟨⟩) => `(EPost.nil.mk)
  | `(epost⟨$x⟩) => `(EPost.cons.mk $x EPost.nil.mk)
  | `(epost⟨$x, $xs,*⟩) => `(EPost.cons.mk $x epost⟨$xs,*⟩)
  | `(post⟨$x⟩) => `(Post.mk (fun _ : PUnit => $x) EPost.nil.mk)
  | `(post⟨$x, $xs,*⟩) => `(Post.mk (fun _ : PUnit => $x) epost⟨$xs,*⟩)

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

@[app_unexpander Post] def unexpandPost : Lean.PrettyPrinter.Unexpander
  | `($(_) PUnit $x $xs) =>
    match xs with
    | `(EPost⟨⟩) => `(Post⟨$x⟩)
    | `(EPost⟨$y⟩) => `(Post⟨$x, $y⟩)
    | `(EPost⟨$y, $ys,*⟩) => `(Post⟨$x, $y, $ys,*⟩)
    | _ => `(Post PUnit $x $xs)
  | `($(_) $α $x $xs) => `(Post $α $x $xs)
  | _ => throw ()

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

@[app_unexpander Post.mk] def unexpandPostMk : Lean.PrettyPrinter.Unexpander
  | `($(_) $post $xs) =>
    match post with
    | `(fun $_ => $x) =>
      match xs with
      | `(epost⟨⟩) => `(post⟨$x⟩)
      | `(epost⟨$y⟩) => `(post⟨$x, $y⟩)
      | `(epost⟨$y, $ys,*⟩) => `(post⟨$x, $y, $ys,*⟩)
      | _ => `(Post.mk $post $xs)
    | `(fun $_ : PUnit => $x) =>
      match xs with
      | `(epost⟨⟩) => `(post⟨$x⟩)
      | `(epost⟨$y⟩) => `(post⟨$x, $y⟩)
      | `(epost⟨$y, $ys,*⟩) => `(post⟨$x, $y, $ys,*⟩)
      | _ => `(Post.mk $post $xs)
    | _ => `(Post.mk $post $xs)
  | _ => throw ()

/-- info: Post⟨Nat, Bool⟩ : Type u_1 -/
#guard_msgs in
#check Post⟨Nat, Bool⟩
/-- info: EPost⟨Nat, Bool, String⟩ : Type -/
#guard_msgs in
#check EPost⟨Nat, Bool, String⟩
/-- info: Post⟨Nat, Bool, String⟩ : Type u_1 -/
#guard_msgs in
#check Post⟨Nat, Bool, String⟩
/-- info: EPost⟨Nat, Bool⟩ : Type -/
#guard_msgs in
#check (EPost.cons Nat (EPost.cons Bool EPost.nil))
/-- info: Post⟨Nat, Bool, String⟩ : Type u_1 -/
#guard_msgs in
#check (Post PUnit Nat (EPost.cons Bool (EPost.cons String EPost.nil)))
/-- info: epost⟨1, true⟩ : EPost⟨Nat, Bool⟩ -/
#guard_msgs in
#check epost⟨1, true⟩
/-- info: post⟨1, true⟩ : Post⟨Nat, Bool⟩ -/
#guard_msgs in
#check post⟨1, true⟩
/-- info: post⟨1, true, "x"⟩ : Post⟨Nat, Bool, String⟩ -/
#guard_msgs in
#check post⟨1, true, "x"⟩

-- Parser/elaborator tests for macro expansions
example : EPost⟨Nat⟩ = EPost.cons Nat EPost.nil := rfl
example : EPost⟨Nat, Bool⟩ = EPost.cons Nat (EPost.cons Bool EPost.nil) := rfl
example : Post⟨Nat, Bool⟩ = Post PUnit Nat (EPost.cons Bool EPost.nil) := rfl
example : Post⟨Nat, Bool, String⟩ = Post PUnit Nat (EPost.cons Bool (EPost.cons String EPost.nil)) := rfl
example : epost⟨1, true⟩ = EPost.cons.mk 1 (EPost.cons.mk true EPost.nil.mk) := rfl
example : post⟨1, true⟩ = Post.mk (fun _ : PUnit => 1) (EPost.cons.mk true EPost.nil.mk) := rfl
example : post⟨1, true, "x"⟩ =
  Post.mk (fun _ : PUnit => 1) (EPost.cons.mk true (EPost.cons.mk "x" EPost.nil.mk)) := rfl
