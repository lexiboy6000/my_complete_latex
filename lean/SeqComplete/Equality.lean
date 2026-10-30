/-!
# Equality, built by hand

We do not use Lean's `=` for elements of our groups. Instead equality is the
inductive type below: the *only* way to prove `a ≐ b` is `MyEq.refl : a ≐ a`,
and the only way to *use* `a ≐ b` is its eliminator `MyEq.rec`, i.e.
"substitute `b` for `a` in any statement".  Everything else
(symmetry, transitivity, congruence) is derived from that one principle.
-/

universe u v w

inductive MyEq {α : Sort u} (a : α) : α → Prop where
  | refl : MyEq a a

infix:50 " ≐ " => MyEq -- \ . = put together give ≐

namespace MyEq

variable {α : Sort u} {β : Sort v} {γ : Sort w} {a b c : α}

/-- Substitution (Leibniz' law): this is just the eliminator `MyEq.rec`. -/
theorem subst {motive : α → Prop} (h : a ≐ b) (ha : motive a) : motive b :=
  @MyEq.rec α a (fun x _ => motive x) ha b h

theorem symm (h : a ≐ b) : b ≐ a :=
  subst (motive := fun x => x ≐ a) h refl

theorem trans (h₁ : a ≐ b) (h₂ : b ≐ c) : a ≐ c :=
  subst (motive := fun x => a ≐ x) h₂ h₁

theorem congrArg (f : α → β) (h : a ≐ b) : f a ≐ f b :=
  subst (motive := fun x => f a ≐ f x) h refl

theorem congrArg₂ (f : α → β → γ) {a a' : α} {b b' : β}
    (h₁ : a ≐ a') (h₂ : b ≐ b') : f a b ≐ f a' b' :=
  subst (motive := fun x => f a b ≐ f a' x) h₂
    (subst (motive := fun x => f a b ≐ f x b) h₁ refl)

/-- Transport a proof of `p a` along `a ≐ b`. -/
theorem mp {p : α → Prop} (h : a ≐ b) : p a → p b := subst h

/-- Lets us write `calc a ≐ b := _  _ ≐ c := _`. -/
instance : @Trans α α α MyEq MyEq MyEq := ⟨trans⟩

end MyEq
