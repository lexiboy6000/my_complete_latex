import SeqComplete.Equality

/-!
# (V1) Abelian groups, built by hand

Paper, Definition (well-valued set), axiom (V1): `(V,+)` is an abelian group.
All axioms are stated with our own equality `≐`.
-/

class AbelianGroup (G : Type) extends Add G, Neg G where
  zero : G
  add_assoc : ∀ a b c : G, (a + b) + c ≐ a + (b + c)
  add_comm  : ∀ a b : G, a + b ≐ b + a
  add_zero  : ∀ a : G, a + zero ≐ a
  add_neg   : ∀ a : G, a + -a ≐ zero

namespace MyR

variable {G : Type} [AbelianGroup G]

instance : OfNat G 0 := ⟨AbelianGroup.zero⟩

/-- `a - b := a + (-b)`. -/
instance : Sub G := ⟨fun a b => a + -b⟩

theorem sub_def (a b : G) : a - b ≐ a + -b := .refl

theorem add_assoc (a b c : G) : a + b + c ≐ a + (b + c) := AbelianGroup.add_assoc a b c
theorem add_comm (a b : G) : a + b ≐ b + a := AbelianGroup.add_comm a b
theorem add_zero (a : G) : a + 0 ≐ a := AbelianGroup.add_zero a
theorem add_neg (a : G) : a + -a ≐ 0 := AbelianGroup.add_neg a

theorem zero_add (a : G) : 0 + a ≐ a := (add_comm 0 a).trans (add_zero a)
theorem neg_add (a : G) : -a + a ≐ 0 := (add_comm (-a) a).trans (add_neg a)
theorem sub_self (a : G) : a - a ≐ 0 := add_neg a

/-! ### congruence: replacing equals by equals inside `+` and `-` -/

theorem add_congr {a a' b b' : G} (h₁ : a ≐ a') (h₂ : b ≐ b') : a + b ≐ a' + b' :=
  MyEq.congrArg₂ (· + ·) h₁ h₂

theorem add_congr_left {a a' : G} (h : a ≐ a') (b : G) : a + b ≐ a' + b :=
  add_congr h .refl

theorem add_congr_right (a : G) {b b' : G} (h : b ≐ b') : a + b ≐ a + b' :=
  add_congr .refl h

theorem neg_congr {a b : G} (h : a ≐ b) : -a ≐ -b := MyEq.congrArg (fun x => -x) h

theorem sub_congr {a a' b b' : G} (h₁ : a ≐ a') (h₂ : b ≐ b') : a - b ≐ a' - b' :=
  add_congr h₁ (neg_congr h₂)

/-! ### cancellation and inverses -/

theorem add_neg_cancel_right (a b : G) : a + b + -b ≐ a :=
  calc a + b + -b ≐ a + (b + -b) := add_assoc a b (-b)
    _ ≐ a + 0 := add_congr_right a (add_neg b)
    _ ≐ a := add_zero a

theorem neg_add_cancel_right (a b : G) : a + -b + b ≐ a :=
  calc a + -b + b ≐ a + (-b + b) := add_assoc a (-b) b
    _ ≐ a + 0 := add_congr_right a (neg_add b)
    _ ≐ a := add_zero a

theorem sub_add_cancel (a b : G) : a - b + b ≐ a := neg_add_cancel_right a b
theorem add_sub_cancel (a b : G) : a + b - b ≐ a := add_neg_cancel_right a b

theorem add_right_cancel {a b c : G} (h : a + c ≐ b + c) : a ≐ b :=
  calc a ≐ a + c + -c := (add_neg_cancel_right a c).symm
    _ ≐ b + c + -c := add_congr_left h (-c)
    _ ≐ b := add_neg_cancel_right b c

/-- Inverses are unique. -/
theorem neg_unique {a b : G} (h : a + b ≐ 0) : b ≐ -a :=
  calc b ≐ 0 + b := (zero_add b).symm
    _ ≐ (-a + a) + b := add_congr_left (neg_add a).symm b
    _ ≐ -a + (a + b) := add_assoc (-a) a b
    _ ≐ -a + 0 := add_congr_right (-a) h
    _ ≐ -a := add_zero (-a)

theorem neg_neg (a : G) : -(-a) ≐ a := (neg_unique (neg_add a)).symm

theorem neg_zero : -(0 : G) ≐ 0 := (neg_unique (add_zero (0 : G))).symm

theorem sub_zero (a : G) : a - 0 ≐ a :=
  (add_congr_right a neg_zero).trans (add_zero a)

/-! ### rearrangements -/

theorem add_add_add_comm (a b c d : G) : (a + b) + (c + d) ≐ (a + c) + (b + d) :=
  calc (a + b) + (c + d) ≐ a + (b + (c + d)) := add_assoc a b (c + d)
    _ ≐ a + ((b + c) + d) := add_congr_right a (add_assoc b c d).symm
    _ ≐ a + ((c + b) + d) := add_congr_right a (add_congr_left (add_comm b c) d)
    _ ≐ a + (c + (b + d)) := add_congr_right a (add_assoc c b d)
    _ ≐ (a + c) + (b + d) := (add_assoc a c (b + d)).symm

theorem neg_add_distrib (a b : G) : -(a + b) ≐ -a + -b :=
  (neg_unique (calc (a + b) + (-a + -b) ≐ (a + -a) + (b + -b) := add_add_add_comm a b (-a) (-b)
      _ ≐ 0 + 0 := add_congr (add_neg a) (add_neg b)
      _ ≐ 0 := add_zero 0)).symm

theorem neg_sub (a b : G) : -(a - b) ≐ b - a :=
  calc -(a + -b) ≐ -a + -(-b) := neg_add_distrib a (-b)
    _ ≐ -a + b := add_congr_right (-a) (neg_neg b)
    _ ≐ b + -a := add_comm (-a) b

/-- `(a - b) + (b - c) = a - c`: the algebra behind the triangle inequality. -/
theorem sub_add_sub (a b c : G) : (a - b) + (b - c) ≐ a - c :=
  calc (a + -b) + (b + -c) ≐ a + (-b + (b + -c)) := add_assoc a (-b) (b + -c)
    _ ≐ a + ((-b + b) + -c) := add_congr_right a (add_assoc (-b) b (-c)).symm
    _ ≐ a + (0 + -c) := add_congr_right a (add_congr_left (neg_add b) (-c))
    _ ≐ a + -c := add_congr_right a (zero_add (-c))

theorem sub_sub_sub (a b c d : G) : (a - b) - (c - d) ≐ (a - c) - (b - d) :=
  calc (a + -b) + -(c + -d) ≐ (a + -b) + (-c + -(-d)) := add_congr_right _ (neg_add_distrib c (-d))
    _ ≐ (a + -c) + (-b + -(-d)) := add_add_add_comm a (-b) (-c) (-(-d))
    _ ≐ (a + -c) + -(b + -d) := add_congr_right _ (neg_add_distrib b (-d)).symm

/-! ### `n • a = a + ⋯ + a` -/

def nsmul : Nat → G → G
  | 0, _ => 0
  | n + 1, a => nsmul n a + a

theorem nsmul_succ (n : Nat) (a : G) : nsmul (n + 1) a ≐ nsmul n a + a := .refl

end MyR
