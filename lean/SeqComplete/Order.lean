import SeqComplete.Group

/-!
# (V2), (V3): ordered Archimedean groups, and `Q`-like sets

Paper, §3.1:
* (V2) `<` is a total order with `a < b → a + c < b + c`;
* (V3) Archimedean: `a, b > 0 → ∃ n, n • a > b`;
* `Q`-like := (V1)–(V3) + dense + nontrivial  (Definition `def:qlike`).
-/

/-- (V1) + (V2): an ordered abelian group. -/
class OrderedAbelianGroup (G : Type) extends AbelianGroup G, LT G where
  lt_irrefl : ∀ a : G, ¬ a < a
  lt_trans : ∀ {a b c : G}, a < b → b < c → a < c
  lt_trichotomy : ∀ a b : G, a < b ∨ a ≐ b ∨ b < a
  add_lt_add_right : ∀ {a b : G}, a < b → ∀ c : G, a + c < b + c

namespace MyR

/-- (V3): Archimedean. -/
class WellValued (G : Type) [OrderedAbelianGroup G] : Prop where
  archimedean : ∀ a b : G, 0 < a → 0 < b → ∃ n : Nat, b < nsmul n a

/-- A `Q`-like set: a dense, nontrivial well-valued set. -/
class QLike (G : Type) [OrderedAbelianGroup G] : Prop extends WellValued G where
  dense : ∀ {a b : G}, a < b → ∃ c, a < c ∧ c < b
  nontrivial : ∃ a : G, ¬ a ≐ 0

section Ordered

variable {G : Type} [OrderedAbelianGroup G]

/-- `a ≤ b` means `a < b` or `a = b` (paper's convention). -/
instance : LE G := ⟨fun a b => a < b ∨ a ≐ b⟩

theorem le_cases {a b : G} (h : a ≤ b) : a < b ∨ a ≐ b := h

theorem lt_irrefl (a : G) : ¬ a < a := OrderedAbelianGroup.lt_irrefl a
theorem lt_trans {a b c : G} : a < b → b < c → a < c := OrderedAbelianGroup.lt_trans
theorem lt_trichotomy (a b : G) : a < b ∨ a ≐ b ∨ b < a := OrderedAbelianGroup.lt_trichotomy a b
theorem add_lt_add_right {a b : G} (h : a < b) (c : G) : a + c < b + c :=
  OrderedAbelianGroup.add_lt_add_right h c

theorem le_of_lt {a b : G} (h : a < b) : a ≤ b := Or.inl h
theorem le_of_eq {a b : G} (h : a ≐ b) : a ≤ b := Or.inr h
theorem le_refl (a : G) : a ≤ a := le_of_eq .refl

/-! ### transitivity, mixing `<`, `≤`, `≐` -/

theorem lt_of_eq_of_lt {a b c : G} (h₁ : a ≐ b) (h₂ : b < c) : a < c :=
  MyEq.subst (motive := fun x => x < c) h₁.symm h₂
theorem lt_of_lt_of_eq {a b c : G} (h₁ : a < b) (h₂ : b ≐ c) : a < c :=
  MyEq.subst (motive := fun x => a < x) h₂ h₁
theorem le_of_eq_of_le {a b c : G} (h₁ : a ≐ b) (h₂ : b ≤ c) : a ≤ c :=
  MyEq.subst (motive := fun x => x ≤ c) h₁.symm h₂
theorem le_of_le_of_eq {a b c : G} (h₁ : a ≤ b) (h₂ : b ≐ c) : a ≤ c :=
  MyEq.subst (motive := fun x => a ≤ x) h₂ h₁

theorem lt_of_lt_of_le {a b c : G} (h₁ : a < b) (h₂ : b ≤ c) : a < c := by
  rcases le_cases h₂ with h₂ | h₂
  · exact lt_trans h₁ h₂
  · exact lt_of_lt_of_eq h₁ h₂

theorem lt_of_le_of_lt {a b c : G} (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  rcases le_cases h₁ with h₁ | h₁
  · exact lt_trans h₁ h₂
  · exact lt_of_eq_of_lt h₁ h₂

theorem le_trans {a b c : G} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  rcases le_cases h₁ with h₁ | h₁
  · exact le_of_lt (lt_of_lt_of_le h₁ h₂)
  · exact le_of_eq_of_le h₁ h₂

instance : @Trans G G G LT.lt LT.lt LT.lt := ⟨lt_trans⟩
instance : @Trans G G G LT.lt LE.le LT.lt := ⟨lt_of_lt_of_le⟩
instance : @Trans G G G LE.le LT.lt LT.lt := ⟨lt_of_le_of_lt⟩
instance : @Trans G G G LE.le LE.le LE.le := ⟨le_trans⟩
instance : @Trans G G G MyEq LT.lt LT.lt := ⟨lt_of_eq_of_lt⟩
instance : @Trans G G G LT.lt MyEq LT.lt := ⟨lt_of_lt_of_eq⟩
instance : @Trans G G G MyEq LE.le LE.le := ⟨le_of_eq_of_le⟩
instance : @Trans G G G LE.le MyEq LE.le := ⟨le_of_le_of_eq⟩

theorem not_lt_of_le {a b : G} (h : a ≤ b) : ¬ b < a := fun h' =>
  lt_irrefl a (lt_of_le_of_lt h h')

theorem le_of_not_lt {a b : G} (h : ¬ b < a) : a ≤ b := by
  rcases lt_trichotomy a b with h' | h' | h'
  · exact le_of_lt h'
  · exact le_of_eq h'
  · exact absurd h' h

/-! ### compatibility of `<` with `+` -/

theorem add_lt_add_left {a b : G} (h : a < b) (c : G) : c + a < c + b :=
  calc c + a ≐ a + c := add_comm c a
    _ < b + c := add_lt_add_right h c
    _ ≐ c + b := add_comm b c

theorem add_le_add_right {a b : G} (h : a ≤ b) (c : G) : a + c ≤ b + c := by
  rcases le_cases h with h | h
  · exact le_of_lt (add_lt_add_right h c)
  · exact le_of_eq (add_congr_left h c)

theorem add_le_add_left {a b : G} (h : a ≤ b) (c : G) : c + a ≤ c + b := by
  rcases le_cases h with h | h
  · exact le_of_lt (add_lt_add_left h c)
  · exact le_of_eq (add_congr_right c h)

/-- Lemma `lem:ineq` (a). -/
theorem add_lt_add_of_lt_of_le {a b c d : G} (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d :=
  lt_of_lt_of_le (add_lt_add_right h₁ c) (add_le_add_left h₂ b)

theorem add_lt_add_of_le_of_lt {a b c d : G} (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d :=
  lt_of_le_of_lt (add_le_add_right h₁ c) (add_lt_add_left h₂ b)

theorem add_lt_add {a b c d : G} (h₁ : a < b) (h₂ : c < d) : a + c < b + d :=
  add_lt_add_of_lt_of_le h₁ (le_of_lt h₂)

theorem add_le_add {a b c d : G} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
  le_trans (add_le_add_right h₁ c) (add_le_add_left h₂ b)

theorem lt_of_add_lt_add_right {a b c : G} (h : a + c < b + c) : a < b :=
  calc a ≐ a + c + -c := (add_neg_cancel_right a c).symm
    _ < b + c + -c := add_lt_add_right h (-c)
    _ ≐ b := add_neg_cancel_right b c

theorem lt_add_of_pos_right (a : G) {b : G} (h : 0 < b) : a < a + b :=
  calc a ≐ a + 0 := (add_zero a).symm
    _ < a + b := add_lt_add_left h a

theorem add_pos {a b : G} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  lt_trans ha (lt_add_of_pos_right a hb)

/-- Lemma `lem:ineq` (b). -/
theorem neg_lt_neg {a b : G} (h : a < b) : -b < -a :=
  calc -b ≐ 0 + -b := (zero_add (-b)).symm
    _ ≐ (a + -a) + -b := add_congr_left (add_neg a).symm (-b)
    _ ≐ a + (-a + -b) := add_assoc a (-a) (-b)
    _ < b + (-a + -b) := add_lt_add_right h (-a + -b)
    _ ≐ b + (-b + -a) := add_congr_right b (add_comm (-a) (-b))
    _ ≐ (b + -b) + -a := (add_assoc b (-b) (-a)).symm
    _ ≐ 0 + -a := add_congr_left (add_neg b) (-a)
    _ ≐ -a := zero_add (-a)

theorem neg_le_neg {a b : G} (h : a ≤ b) : -b ≤ -a := by
  rcases le_cases h with h | h
  · exact le_of_lt (neg_lt_neg h)
  · exact le_of_eq (neg_congr h).symm

theorem neg_pos_of_neg {a : G} (h : a < 0) : 0 < -a :=
  lt_of_eq_of_lt neg_zero.symm (neg_lt_neg h)

theorem neg_nonpos_of_nonneg {a : G} (h : 0 ≤ a) : -a ≤ 0 :=
  le_of_le_of_eq (neg_le_neg h) neg_zero

theorem sub_pos {a b : G} (h : a < b) : 0 < b - a :=
  calc (0 : G) ≐ a + -a := (add_neg a).symm
    _ < b + -a := add_lt_add_right h (-a)

theorem lt_of_sub_pos {a b : G} (h : 0 < b - a) : a < b :=
  calc a ≐ 0 + a := (zero_add a).symm
    _ < b - a + a := add_lt_add_right h a
    _ ≐ b := sub_add_cancel b a

theorem sub_le_sub {a b c d : G} (h₁ : a ≤ b) (h₂ : c ≤ d) : a - d ≤ b - c :=
  add_le_add h₁ (neg_le_neg h₂)

/-- `a - b < c → a < c + b`. -/
theorem lt_add_of_sub_lt {a b c : G} (h : a - b < c) : a < c + b :=
  calc a ≐ a - b + b := (sub_add_cancel a b).symm
    _ < c + b := add_lt_add_right h b

/-! ### absolute value `|a| := max(a, -a)` -/

theorem abs_exists (a : G) : ∃ y : G, (0 ≤ a ∧ y ≐ a) ∨ (a < 0 ∧ y ≐ -a) := by
  rcases lt_trichotomy a 0 with h | h | h
  · exact ⟨-a, Or.inr ⟨h, .refl⟩⟩
  · exact ⟨a, Or.inl ⟨le_of_eq h.symm, .refl⟩⟩
  · exact ⟨a, Or.inl ⟨le_of_lt h, .refl⟩⟩

/-- `|a|`, chosen by the specification `abs_exists` (no `if`, no Lean `=`). -/
noncomputable def abs (a : G) : G := Classical.choose (abs_exists a)

theorem abs_spec (a : G) : (0 ≤ a ∧ abs a ≐ a) ∨ (a < 0 ∧ abs a ≐ -a) :=
  Classical.choose_spec (abs_exists a)

theorem le_abs_self (a : G) : a ≤ abs a := by
  rcases abs_spec a with ⟨_, h⟩ | ⟨ha, h⟩
  · exact le_of_eq h.symm
  · exact le_of_lt (lt_trans ha (lt_of_lt_of_eq (neg_pos_of_neg ha) h.symm))

theorem neg_le_abs (a : G) : -a ≤ abs a := by
  rcases abs_spec a with ⟨ha, h⟩ | ⟨_, h⟩
  · exact le_trans (neg_nonpos_of_nonneg ha) (le_of_le_of_eq ha h.symm)
  · exact le_of_eq h.symm

theorem abs_nonneg (a : G) : 0 ≤ abs a := by
  rcases abs_spec a with ⟨ha, h⟩ | ⟨ha, h⟩
  · exact le_of_le_of_eq ha h.symm
  · exact le_of_lt (lt_of_lt_of_eq (neg_pos_of_neg ha) h.symm)

theorem abs_le_of {a c : G} (h₁ : a ≤ c) (h₂ : -a ≤ c) : abs a ≤ c := by
  rcases abs_spec a with ⟨_, h⟩ | ⟨_, h⟩
  · exact le_of_eq_of_le h h₁
  · exact le_of_eq_of_le h h₂

theorem abs_lt_of {a c : G} (h₁ : a < c) (h₂ : -a < c) : abs a < c := by
  rcases abs_spec a with ⟨_, h⟩ | ⟨_, h⟩
  · exact lt_of_eq_of_lt h h₁
  · exact lt_of_eq_of_lt h h₂

theorem abs_zero : abs (0 : G) ≐ 0 := by
  rcases abs_spec (0 : G) with ⟨_, h⟩ | ⟨h0, _⟩
  · exact h
  · exact absurd h0 (lt_irrefl 0)

theorem abs_neg_le (a : G) : abs (-a) ≤ abs a :=
  abs_le_of (neg_le_abs a) (le_of_eq_of_le (neg_neg a) (le_abs_self a))

/-- Lemma `lem:ineq` (c): the triangle inequality for `|·|`. -/
theorem abs_add (a b : G) : abs (a + b) ≤ abs a + abs b :=
  abs_le_of (add_le_add (le_abs_self a) (le_abs_self b))
    (le_of_eq_of_le (neg_add_distrib a b) (add_le_add (neg_le_abs a) (neg_le_abs b)))

theorem abs_sub_le (a b : G) : abs (a - b) ≤ abs a + abs b :=
  le_trans (abs_add a (-b)) (add_le_add_left (abs_neg_le b) (abs a))

theorem abs_sub_comm_le (a b : G) : abs (a - b) ≤ abs (b - a) :=
  abs_le_of (le_of_eq_of_le (neg_sub b a).symm (neg_le_abs (b - a)))
    (le_of_eq_of_le (neg_sub a b) (le_abs_self (b - a)))

theorem abs_sub_abs_le (a b : G) : abs a - abs b ≤ abs (a - b) :=
  calc abs a - abs b ≐ abs (a - b + b) - abs b :=
        sub_congr (MyEq.congrArg abs (sub_add_cancel a b).symm) .refl
    _ ≤ (abs (a - b) + abs b) - abs b := add_le_add_right (abs_add (a - b) b) _
    _ ≐ abs (a - b) := add_sub_cancel _ _

/-- Lemma `lem:ineq` (c): `||a| - |b|| ≤ |a - b|`. -/
theorem abs_abs_sub_abs_le (a b : G) : abs (abs a - abs b) ≤ abs (a - b) :=
  abs_le_of (abs_sub_abs_le a b)
    (le_of_eq_of_le (neg_sub _ _) (le_trans (abs_sub_abs_le b a) (abs_sub_comm_le b a)))

/-! ### the natural metric `d(x,y) = |x - y|` (Definition `def:natmetric`) -/

noncomputable def d (x y : G) : G := abs (x - y)

theorem d_nonneg (x y : G) : 0 ≤ d x y := abs_nonneg _

theorem d_self (x : G) : d x x ≐ 0 :=
  (MyEq.congrArg abs (sub_self x)).trans abs_zero

theorem d_comm_le (x y : G) : d x y ≤ d y x := abs_sub_comm_le x y

theorem d_triangle (x y z : G) : d x z ≤ d x y + d y z :=
  calc abs (x - z) ≐ abs ((x - y) + (y - z)) := MyEq.congrArg abs (sub_add_sub x y z).symm
    _ ≤ abs (x - y) + abs (y - z) := abs_add _ _

/-- Distances move by at most the movement of the endpoints:
`| d(a,b) - d(c,e) | ≤ d(a,c) + d(b,e)`. -/
theorem d_d_le (a b c e : G) : d (d a b) (d c e) ≤ d a c + d b e :=
  calc abs (abs (a - b) - abs (c - e)) ≤ abs ((a - b) - (c - e)) := abs_abs_sub_abs_le _ _
    _ ≐ abs ((a - c) - (b - e)) := MyEq.congrArg abs (sub_sub_sub a b c e)
    _ ≤ abs (a - c) + abs (b - e) := abs_sub_le _ _

/-! ### `n • a` -/

theorem nsmul_le_nsmul_of_le {a b : G} (h : a ≤ b) : ∀ n : Nat, nsmul n a ≤ nsmul n b
  | 0 => le_refl 0
  | n + 1 => add_le_add (nsmul_le_nsmul_of_le h n) h

theorem nsmul_le_nsmul {ε : G} (hε : 0 < ε) {m n : Nat} (h : m ≤ n) : nsmul m ε ≤ nsmul n ε := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => exact le_refl _
  | succ k ih =>
    exact le_trans (ih (Nat.le_add_right m k)) (le_of_lt (lt_add_of_pos_right _ hε))

end Ordered

/-! ### properties of `Q`-like sets -/

section QLike

variable {G : Type} [OrderedAbelianGroup G] [QLike G]

/-- Lemma `lem:halving`: `ε > 0 → ∃ η > 0, η + η ≤ ε` ("`ε/2`"). -/
theorem exists_half {ε : G} (hε : 0 < ε) : ∃ η, 0 < η ∧ η + η ≤ ε := by
  obtain ⟨δ, h0δ, hδε⟩ := QLike.dense hε
  rcases lt_trichotomy (δ + δ) ε with h | h | h
  · exact ⟨δ, h0δ, le_of_lt h⟩
  · exact ⟨δ, h0δ, le_of_eq h⟩
  · -- `δ` is more than half of `ε`, so `ε - δ` is less than half
    refine ⟨ε - δ, sub_pos hδε, le_of_lt (lt_of_add_lt_add_right (c := δ + δ) ?_)⟩
    calc (ε - δ) + (ε - δ) + (δ + δ) ≐ (ε - δ + δ) + (ε - δ + δ) := add_add_add_comm _ _ _ _
      _ ≐ ε + ε := add_congr (sub_add_cancel ε δ) (sub_add_cancel ε δ)
      _ < ε + (δ + δ) := add_lt_add_left h ε

theorem exists_pos : ∃ p : G, 0 < p := by
  obtain ⟨a, ha⟩ := (QLike.nontrivial : ∃ a : G, ¬ a ≐ 0)
  rcases lt_trichotomy a 0 with h | h | h
  · exact ⟨-a, neg_pos_of_neg h⟩
  · exact absurd h ha
  · exact ⟨a, h⟩

/-! ### Lemma `lem:nullseq`: a sequence `e_n` tending to zero, `e_{n+1} + e_{n+1} ≤ e_n` -/

/-- The sequence together with its positivity (so the recursion can halve it). -/
noncomputable def eSub (G : Type) [OrderedAbelianGroup G] [QLike G] : Nat → {x : G // 0 < x}
  | 0 => ⟨Classical.choose (exists_pos (G := G)), Classical.choose_spec (exists_pos (G := G))⟩
  | n + 1 => ⟨Classical.choose (exists_half (eSub G n).2),
              (Classical.choose_spec (exists_half (eSub G n).2)).1⟩

/-- `e n` "looks like `(1/2)^n`". -/
noncomputable def e (G : Type) [OrderedAbelianGroup G] [QLike G] (n : Nat) : G := (eSub G n).1

theorem e_pos (n : Nat) : 0 < e G n := (eSub G n).2

theorem e_half (n : Nat) : e G (n + 1) + e G (n + 1) ≤ e G n :=
  (Classical.choose_spec (exists_half (eSub G n).2)).2

theorem e_succ_lt (n : Nat) : e G (n + 1) < e G n :=
  lt_of_lt_of_le (lt_add_of_pos_right _ (e_pos (n + 1))) (e_half n)

/-- `e_{k+2} + e_{k+2} + e_{k+2} + e_{k+2} ≤ e_k` ("`4 (ε/4) ≤ ε`"). -/
theorem e_quarter (k : Nat) : (e G (k + 2) + e G (k + 2)) + (e G (k + 2) + e G (k + 2)) ≤ e G k :=
  le_trans (add_le_add (e_half (k + 1)) (e_half (k + 1))) (e_half k)

/-- `n • e_n + e_n ≤ e_0`: this is where `e_n ≈ e_0 / 2^n ≤ e_0 / n` is used. -/
theorem nsmul_e_le : ∀ n : Nat, nsmul n (e G n) + e G n ≤ e G 0
  | 0 => le_of_eq (zero_add _)
  | n + 1 =>
    calc nsmul (n + 1) (e G (n + 1)) + e G (n + 1)
        ≐ nsmul n (e G (n + 1)) + (e G (n + 1) + e G (n + 1)) := add_assoc _ _ _
      _ ≤ nsmul n (e G n) + e G n :=
          add_le_add (nsmul_le_nsmul_of_le (le_of_lt (e_succ_lt n)) n) (e_half n)
      _ ≤ e G 0 := nsmul_e_le n

/-- `e_n → 0`. This is the one place we use the Archimedean property (V3). -/
theorem e_small {ε : G} (hε : 0 < ε) : ∃ N : Nat, ∀ n, N ≤ n → e G n < ε := by
  obtain ⟨m, hm⟩ := WellValued.archimedean ε (e G 0) hε (e_pos 0)
  refine ⟨m, fun n hn => ?_⟩
  rcases lt_trichotomy (e G n) ε with h | h | h
  · exact h
  all_goals
    have hεe : ε ≤ e G n := by
      first
      | exact le_of_eq h.symm
      | exact le_of_lt h
    exfalso
    apply lt_irrefl (nsmul m ε)
    calc nsmul m ε ≤ nsmul n ε := nsmul_le_nsmul hε hn
      _ ≤ nsmul n (e G n) := nsmul_le_nsmul_of_le hεe n
      _ < nsmul n (e G n) + e G n := lt_add_of_pos_right _ (e_pos n)
      _ ≤ e G 0 := nsmul_e_le n
      _ < nsmul m ε := hm

end QLike

end MyR
