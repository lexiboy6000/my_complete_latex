import SeqComplete.Order

/-!
# Cauchy sequences and the construction of `Q̄`  (paper §4.1, Steps 1–3b)

* `IsCauchy x`  : `∀ ε > 0, ∃ N, ∀ n > N, d(x_n, x_N) < ε`.
* `Qbar G`      : the Cauchy sequences in `G` (paper: the set `S`).
* `X ≈ Y`       : *equality* in `Q̄`, `d(x_n, y_n) → 0`.  We never pass to a
                  quotient: equality of real numbers is a relation we built.
* `dbar X Y`    : `[(d(x_n, y_n))]`, again an element of `Q̄`.
* `X < Y`       : `∃ δ > 0, ∃ N, ∀ n > N, y_n - x_n ≥ δ`.
* `ι q`         : the constant sequence `(q, q, q, …)`.
-/

namespace MyR

variable {G : Type} [OrderedAbelianGroup G] [QLike G]

def IsCauchy (x : Nat → G) : Prop :=
  ∀ ε : G, 0 < ε → ∃ N : Nat, ∀ n, N < n → d (x n) (x N) < ε

/-- Moving both late terms to `x_N` (paper, Figure `fig:cauchy2`):
any two late terms are close. -/
theorem IsCauchy.pairs {x : Nat → G} (hx : IsCauchy x) {ε : G} (hε : 0 < ε) :
    ∃ N : Nat, ∀ m n, N < m → N < n → d (x m) (x n) < ε := by
  obtain ⟨η, hη, hηε⟩ := exists_half hε
  obtain ⟨N, hN⟩ := hx η hη
  refine ⟨N, fun m n hm hn => ?_⟩
  calc d (x m) (x n) ≤ d (x m) (x N) + d (x N) (x n) := d_triangle _ _ _
    _ < η + η := add_lt_add_of_lt_of_le (hN m hm) (le_of_lt (lt_of_le_of_lt (d_comm_le _ _) (hN n hn)))
    _ ≤ ε := hηε

omit [QLike G] in
theorem isCauchy_of_pairs {x : Nat → G}
    (h : ∀ ε : G, 0 < ε → ∃ N : Nat, ∀ m n, N < m → N < n → d (x m) (x n) < ε) : IsCauchy x := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N + 1, fun n hn => hN n (N + 1) (by omega) (by omega)⟩

/-! ### Step 1: the ambient space -/

/-- `Q̄`: Cauchy sequences in `G`.  (Its equality is `≈` below.) -/
def Qbar (G : Type) [OrderedAbelianGroup G] [QLike G] : Type := {x : Nat → G // IsCauchy x}

/-- Read `X n` as the `n`-th term `x_n` of a representative. -/
instance : CoeFun (Qbar G) (fun _ => Nat → G) := ⟨Subtype.val⟩

/-- Equality in `Q̄`: `(x_n) ∼ (y_n) ⟺ d-lim d(x_n, y_n) = 0`. -/
def Qbar.Equiv (X Y : Qbar G) : Prop :=
  ∀ ε : G, 0 < ε → ∃ N : Nat, ∀ n, N < n → d (X n) (Y n) < ε

instance : HasEquiv (Qbar G) := ⟨Qbar.Equiv⟩

/-- `∼` is an equivalence relation. -/
theorem Qbar.equiv_refl (X : Qbar G) : X ≈ X := fun _ hε =>
  ⟨0, fun n _ => lt_of_eq_of_lt (d_self (X n)) hε⟩

theorem Qbar.equiv_symm {X Y : Qbar G} (h : X ≈ Y) : Y ≈ X := fun ε hε => by
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => lt_of_le_of_lt (d_comm_le _ _) (hN n hn)⟩

theorem Qbar.equiv_trans {X Y Z : Qbar G} (h₁ : X ≈ Y) (h₂ : Y ≈ Z) : X ≈ Z := fun ε hε => by
  obtain ⟨η, hη, hηε⟩ := exists_half hε
  obtain ⟨N₁, hN₁⟩ := h₁ η hη
  obtain ⟨N₂, hN₂⟩ := h₂ η hη
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  calc d (X n) (Z n) ≤ d (X n) (Y n) + d (Y n) (Z n) := d_triangle _ _ _
    _ < η + η := add_lt_add (hN₁ n (by omega)) (hN₂ n (by omega))
    _ ≤ ε := hηε

/-! ### Step 2: the distance `d̄` -/

theorem dbar_isCauchy (X Y : Qbar G) : IsCauchy (fun n => d (X n) (Y n)) := by
  apply isCauchy_of_pairs
  intro ε hε
  obtain ⟨η, hη, hηε⟩ := exists_half hε
  obtain ⟨N₁, hN₁⟩ := X.2.pairs hη
  obtain ⟨N₂, hN₂⟩ := Y.2.pairs hη
  refine ⟨max N₁ N₂, fun m n hm hn => ?_⟩
  calc d (d (X m) (Y m)) (d (X n) (Y n)) ≤ d (X m) (X n) + d (Y m) (Y n) := d_d_le _ _ _ _
    _ < η + η := add_lt_add (hN₁ m n (by omega) (by omega)) (hN₂ m n (by omega) (by omega))
    _ ≤ ε := hηε

/-- `d̄([(x_n)], [(y_n)]) := [(d(x_n, y_n))]`. -/
noncomputable def dbar (X Y : Qbar G) : Qbar G := ⟨fun n => d (X n) (Y n), dbar_isCauchy X Y⟩

/-- `d̄` is well defined (respects `≈`). -/
theorem dbar_congr {X X' Y Y' : Qbar G} (hX : X ≈ X') (hY : Y ≈ Y') :
    dbar X Y ≈ dbar X' Y' := fun ε hε => by
  obtain ⟨η, hη, hηε⟩ := exists_half hε
  obtain ⟨N₁, hN₁⟩ := hX η hη
  obtain ⟨N₂, hN₂⟩ := hY η hη
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  calc d (d (X n) (Y n)) (d (X' n) (Y' n)) ≤ d (X n) (X' n) + d (Y n) (Y' n) := d_d_le _ _ _ _
    _ < η + η := add_lt_add (hN₁ n (by omega)) (hN₂ n (by omega))
    _ ≤ ε := hηε

/-! ### Step 3: `ι`, zero, and the order -/

/-- `ι(q) := [(q, q, q, …)]`. -/
def iota (q : G) : Qbar G :=
  ⟨fun _ => q, fun _ hε => ⟨0, fun _ _ => lt_of_eq_of_lt (d_self q) hε⟩⟩

instance : OfNat (Qbar G) 0 := ⟨iota 0⟩

/-- `X < Y ⟺ Y - X > 0 ⟺ ∃ δ > 0, ∃ N, ∀ n > N, y_n - x_n ≥ δ`. -/
def Qbar.lt (X Y : Qbar G) : Prop :=
  ∃ δ : G, 0 < δ ∧ ∃ N : Nat, ∀ n, N < n → δ ≤ Y n - X n

instance : LT (Qbar G) := ⟨Qbar.lt⟩

/-- `<` on `Q̄` is well defined (respects `≈`). -/
theorem Qbar.lt_congr {X X' Y Y' : Qbar G} (hX : X ≈ X') (hY : Y ≈ Y') (h : X < Y) : X' < Y' := by
  obtain ⟨δ, hδ, N, hN⟩ := h
  obtain ⟨η, hη, hηδ⟩ := exists_half hδ
  obtain ⟨μ, hμ, hμη⟩ := exists_half hη
  obtain ⟨N₁, hN₁⟩ := hX μ hμ
  obtain ⟨N₂, hN₂⟩ := hY μ hμ
  refine ⟨η, hη, max N (max N₁ N₂), fun n hn => le_of_lt ?_⟩
  -- `(y - x) - (y' - x') = (y - y') - (x - x')` is smaller than `μ + μ ≤ η`
  have hsmall : (Y n - X n) - (Y' n - X' n) < η :=
    calc (Y n - X n) - (Y' n - X' n) ≤ abs ((Y n - X n) - (Y' n - X' n)) := le_abs_self _
      _ ≐ abs ((Y n - Y' n) - (X n - X' n)) := MyEq.congrArg abs (sub_sub_sub _ _ _ _)
      _ ≤ d (Y n) (Y' n) + d (X n) (X' n) := abs_sub_le _ _
      _ < μ + μ := add_lt_add (hN₂ n (by omega)) (hN₁ n (by omega))
      _ ≤ η := hμη
  apply lt_of_add_lt_add_right (c := η)
  calc η + η ≤ δ := hηδ
    _ ≤ Y n - X n := hN n (by omega)
    _ < η + (Y' n - X' n) := lt_add_of_sub_lt hsmall
    _ ≐ (Y' n - X' n) + η := add_comm _ _

theorem iota_pos {q : G} (hq : 0 < q) : (0 : Qbar G) < iota q :=
  ⟨q, hq, 0, fun _ _ => le_of_eq (sub_zero q).symm⟩

/-- The core idea (boxed in the paper):
`d̄([a_n], [b_n]) < ι(ε) ⟹ ∃ N, ∀ n > N, |a_n - b_n| < ε`. -/
theorem close_of_dbar_lt {A B : Qbar G} {ε : G} (h : dbar A B < iota ε) :
    ∃ N : Nat, ∀ n, N < n → d (A n) (B n) < ε := by
  obtain ⟨δ, hδ, N, hN⟩ := h
  exact ⟨N, fun n hn => lt_of_sub_pos (lt_of_lt_of_le hδ (hN n hn))⟩

end MyR
