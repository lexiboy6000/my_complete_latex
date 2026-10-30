import SeqComplete.Cauchy

/-!
# Completeness proof via Sequences  (paper §5)

Let `(X_n)` be Cauchy in `(Q̄, d̄)`. Each `X_n` *is* a Cauchy sequence
`(a^{(n)}_j)_j` in `G` (we never quotiented, so no choice of representatives is
needed), and we write `X n j` for `a^{(n)}_j`.  Picture the `X_n` as the rows
of an infinite matrix ("a sequence of sequences").

* **rows**    `N_k` (here `R k`): late rows are `e_k`-close to each other;
* **columns** `j_k` (here `J k`): far enough right that
  (ii) row `N_k` is `e_k`-Cauchy past `j_k`, and
  (iii) rows `N_{k+1}` and `N_k` are `e_k`-close past `j_{k+1}` (the core idea);
* **limit**   the diagonal `L := [(a^{(N_k)}_{j_k})_k]`.

Then: Step 1 (hangman) `L` is Cauchy; Step 2 (staircase) `X_n → L`.

The paper takes `N_k`, `j_k` minimal; we only need *some* such indices, so we
pick them with `Classical.choose` and force monotonicity with `max`.
-/

namespace MyR

noncomputable section

variable {G : Type} [OrderedAbelianGroup G] [QLike G]

/-- `(X_n)` is Cauchy in `(Q̄, d̄)`, with `ε` ranging over `Q̄` itself. -/
def QbarCauchy (X : Nat → Qbar G) : Prop :=
  ∀ ε : Qbar G, 0 < ε → ∃ N : Nat, ∀ n, N < n → dbar (X n) (X N) < ε

/-- `d̄-lim X_n = L`, with `ε` ranging over `Q̄` itself. -/
def QbarLim (X : Nat → Qbar G) (L : Qbar G) : Prop :=
  ∀ ε : Qbar G, 0 < ε → ∃ N : Nat, ∀ n, N < n → dbar (X n) L < ε

/-- A strictly increasing index sequence is monotone. -/
theorem mono_of_lt_succ {f : Nat → Nat} (h : ∀ k, f k < f (k + 1)) {k m : Nat} (hkm : k ≤ m) :
    f k ≤ f m := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hkm
  induction t with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    show f k ≤ f (k + t + 1)
    have := h (k + t); have := ih (Nat.le_add_right k t); omega

section Construction

variable {X : Nat → Qbar G} (hX : QbarCauchy X)

/-! ## Step 1: the rows `N_k` -/

/-- Past `C k`, every row is within `e_{k+1}` of row `C k` (Cauchy in `Q̄` with `ε = ι(e_{k+1})`). -/
def C (k : Nat) : Nat := Classical.choose (hX (iota (e G (k + 1))) (iota_pos (e_pos (k + 1))))

theorem C_spec (k : Nat) : ∀ n, C hX k < n → dbar (X n) (X (C hX k)) < iota (e G (k + 1)) :=
  Classical.choose_spec (hX (iota (e G (k + 1))) (iota_pos (e_pos (k + 1))))

/-- Any two rows past `C k` are eventually `e_k`-close, term by term. -/
theorem late_close (k : Nat) {m n : Nat} (hm : C hX k < m) (hn : C hX k < n) :
    ∃ M : Nat, ∀ j, M < j → d (X m j) (X n j) < e G k := by
  obtain ⟨M₁, h₁⟩ := close_of_dbar_lt (C_spec hX k m hm)
  obtain ⟨M₂, h₂⟩ := close_of_dbar_lt (C_spec hX k n hn)
  refine ⟨max M₁ M₂, fun j hj => ?_⟩
  calc d (X m j) (X n j) ≤ d (X m j) (X (C hX k) j) + d (X (C hX k) j) (X n j) := d_triangle _ _ _
    _ < e G (k + 1) + e G (k + 1) :=
        add_lt_add (h₁ j (by omega)) (lt_of_le_of_lt (d_comm_le _ _) (h₂ j (by omega)))
    _ ≤ e G k := e_half k

/-- The rows `N_k`: past `C k`, and strictly increasing. -/
def R : Nat → Nat
  | 0 => C hX 0 + 1
  | k + 1 => max (R k) (C hX (k + 1)) + 1

theorem R_lt_succ (k : Nat) : R hX k < R hX (k + 1) := by
  show R hX k < max (R hX k) (C hX (k + 1)) + 1; omega

theorem C_lt_R (k : Nat) : C hX k < R hX k := by
  cases k with
  | zero => show C hX 0 < C hX 0 + 1; omega
  | succ k => show C hX (k + 1) < max (R hX k) (C hX (k + 1)) + 1; omega

theorem C_lt_R_of_le {k m : Nat} (h : k ≤ m) : C hX k < R hX m :=
  Nat.lt_of_lt_of_le (C_lt_R hX k) (mono_of_lt_succ (R_lt_succ hX) h)

/-! ## Step 2: the columns `j_k` -/

/-- (ii) row `N_k` is `e_k`-Cauchy past `D k`. -/
def D (k : Nat) : Nat := Classical.choose ((X (R hX k)).2.pairs (e_pos (G := G) k))

theorem D_spec (k : Nat) :
    ∀ i j, D hX k < i → D hX k < j → d (X (R hX k) i) (X (R hX k) j) < e G k :=
  Classical.choose_spec ((X (R hX k)).2.pairs (e_pos (G := G) k))

/-- (iii) the core idea: rows `N_{k+1}` and `N_k` are `e_k`-close past `E k`. -/
def E (k : Nat) : Nat :=
  Classical.choose (late_close hX k (C_lt_R_of_le hX (Nat.le_succ k)) (C_lt_R hX k))

theorem E_spec (k : Nat) : ∀ j, E hX k < j → d (X (R hX (k + 1)) j) (X (R hX k) j) < e G k :=
  Classical.choose_spec (late_close hX k (C_lt_R_of_le hX (Nat.le_succ k)) (C_lt_R hX k))

/-- The columns `j_k`: past (ii) and (iii), and strictly increasing (iv). -/
def J : Nat → Nat
  | 0 => D hX 0 + 1
  | k + 1 => max (max (J k) (D hX (k + 1))) (E hX k) + 1

theorem J_lt_succ (k : Nat) : J hX k < J hX (k + 1) := by
  show J hX k < max (max (J hX k) (D hX (k + 1))) (E hX k) + 1; omega

theorem J_mono {k m : Nat} (h : k ≤ m) : J hX k ≤ J hX m := mono_of_lt_succ (J_lt_succ hX) h

theorem D_lt_J (k : Nat) : D hX k < J hX k := by
  cases k with
  | zero => show D hX 0 < D hX 0 + 1; omega
  | succ k => show D hX (k + 1) < max (max (J hX k) (D hX (k + 1))) (E hX k) + 1; omega

theorem E_lt_J (k : Nat) : E hX k < J hX (k + 1) := by
  show E hX k < max (max (J hX k) (D hX (k + 1))) (E hX k) + 1; omega

/-! ## The hangman: walking down the column `j`, from row `N_{k+m}` up to row `N_k`

`d(a^{(N_{k+m})}_j, a^{(N_k)}_j) < e_k + e_{k+1} + ⋯ + e_{k+m-1}`, and the
geometric series (Lemma `lem:geom`) is built into the induction:
we carry `+ 2 e_{k+m}` along and show the total never exceeds `2 e_k`. -/

theorem hangman (k : Nat) : ∀ m j, J hX (k + m) ≤ j →
    d (X (R hX (k + m)) j) (X (R hX k) j) + (e G (k + m) + e G (k + m)) ≤ e G k + e G k
  | 0, j, _ => by
    show d (X (R hX k) j) (X (R hX k) j) + (e G k + e G k) ≤ e G k + e G k
    exact le_of_eq ((add_congr_left (d_self _) _).trans (zero_add _))
  | m + 1, j, hj => by
    show d (X (R hX (k + m + 1)) j) (X (R hX k) j) + (e G (k + m + 1) + e G (k + m + 1))
      ≤ e G k + e G k
    have hjm : J hX (k + m) ≤ j := Nat.le_trans (Nat.le_of_lt (J_lt_succ hX (k + m))) hj
    have hE := E_spec hX (k + m) j (Nat.lt_of_lt_of_le (E_lt_J hX (k + m)) hj)
    have ih := hangman k m j hjm
    -- a = row N_{k+m+1}, b = row N_{k+m}, c = row N_k, all at column j
    refine le_of_lt ?_
    calc d (X (R hX (k + m + 1)) j) (X (R hX k) j) + (e G (k + m + 1) + e G (k + m + 1))
        ≤ (d (X (R hX (k + m + 1)) j) (X (R hX (k + m)) j) + d (X (R hX (k + m)) j) (X (R hX k) j))
            + e G (k + m) := add_le_add (d_triangle _ _ _) (e_half (k + m))
      _ < (e G (k + m) + d (X (R hX (k + m)) j) (X (R hX k) j)) + e G (k + m) :=
          add_lt_add_right (add_lt_add_right hE _) _
      _ ≐ d (X (R hX (k + m)) j) (X (R hX k) j) + (e G (k + m) + e G (k + m)) :=
          (add_congr_left (add_comm _ _) _).trans (add_assoc _ _ _)
      _ ≤ e G k + e G k := ih

/-- For `k ≤ m` and `j ≥ j_m`: `d(a^{(N_m)}_j, a^{(N_k)}_j) < 2 e_k`, for *all* `m`. -/
theorem hangman_lt {k m j : Nat} (hkm : k ≤ m) (hj : J hX m ≤ j) :
    d (X (R hX m) j) (X (R hX k) j) < e G k + e G k := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hkm
  calc d (X (R hX (k + t)) j) (X (R hX k) j)
      < d (X (R hX (k + t)) j) (X (R hX k) j) + (e G (k + t) + e G (k + t)) :=
        lt_add_of_pos_right _ (add_pos (e_pos _) (e_pos _))
    _ ≤ e G k + e G k := hangman hX k t j hj

/-! ## Step 1 of the proof: the diagonal `(a^{(N_k)}_{j_k})_k` is Cauchy -/

theorem diag_isCauchy : IsCauchy (fun k => X (R hX k) (J hX k)) := by
  intro ε hε
  obtain ⟨K, hK⟩ := e_small hε
  refine ⟨K + 2, fun n hn => ?_⟩
  show d (X (R hX n) (J hX n)) (X (R hX (K + 2)) (J hX (K + 2))) < ε
  -- go down column `j_n` from row `N_n` to row `N_{K+2}` (hangman) ...
  have h₁ : d (X (R hX n) (J hX n)) (X (R hX (K + 2)) (J hX n)) < e G (K + 2) + e G (K + 2) :=
    hangman_lt hX (by omega) (Nat.le_refl _)
  -- ... then along row `N_{K+2}` from column `j_n` to column `j_{K+2}` (row is Cauchy)
  have h₂ : d (X (R hX (K + 2)) (J hX n)) (X (R hX (K + 2)) (J hX (K + 2))) < e G (K + 2) :=
    D_spec hX (K + 2) _ _
      (by have := D_lt_J hX (K + 2); have := J_mono hX (show K + 2 ≤ n by omega); omega)
      (D_lt_J hX (K + 2))
  calc d (X (R hX n) (J hX n)) (X (R hX (K + 2)) (J hX (K + 2)))
      ≤ d (X (R hX n) (J hX n)) (X (R hX (K + 2)) (J hX n))
        + d (X (R hX (K + 2)) (J hX n)) (X (R hX (K + 2)) (J hX (K + 2))) := d_triangle _ _ _
    _ < (e G (K + 2) + e G (K + 2)) + e G (K + 2) := add_lt_add h₁ h₂
    _ < (e G (K + 2) + e G (K + 2)) + (e G (K + 2) + e G (K + 2)) :=
        add_lt_add_left (lt_add_of_pos_right _ (e_pos _)) _
    _ ≤ e G K := e_quarter K
    _ < ε := hK K (Nat.le_refl K)

/-- The limit `L := [(a^{(N_k)}_{j_k})_{k ∈ ℕ}] ∈ Q̄`. -/
def diag : Qbar G := ⟨fun k => X (R hX k) (J hX k), diag_isCauchy hX⟩

/-! ## Step 2 of the proof: `X_n → L` (the staircase)

For `n > N_k` and `j` large, compare `a^{(n)}_j` with the diagonal term
`a^{(N_j)}_{j_j}` in three moves:
`a^{(n)}_j → a^{(N_k)}_j` (late rows are close),
`a^{(N_k)}_j → a^{(N_k)}_{j_j}` (row `N_k` is Cauchy),
`a^{(N_k)}_{j_j} → a^{(N_j)}_{j_j}` (hangman down column `j_j`). -/

theorem diag_lim : QbarLim X (diag hX) := by
  intro ε hε
  obtain ⟨δ, hδ, N₀, hN₀⟩ := hε
  obtain ⟨K, hK⟩ := e_small hδ
  -- work with `k = K + 2`, so that `4 e_k ≤ e_K < δ`
  refine ⟨R hX (K + 2), fun n hn => ?_⟩
  obtain ⟨M₁, hM₁⟩ := late_close hX (K + 2) (m := n) (n := R hX (K + 2))
    (Nat.lt_trans (C_lt_R hX (K + 2)) hn) (C_lt_R hX (K + 2))
  refine ⟨δ - e G K, sub_pos (hK K (Nat.le_refl K)),
    max (max N₀ M₁) (max (D hX (K + 2)) (K + 2)), fun j hj => ?_⟩
  show δ - e G K ≤ ε j - d (X n j) (X (R hX j) (J hX j))
  have hk : K + 2 ≤ j := by omega
  have ha : d (X n j) (X (R hX (K + 2)) j) < e G (K + 2) := hM₁ j (by omega)
  have hb : d (X (R hX (K + 2)) j) (X (R hX (K + 2)) (J hX j)) < e G (K + 2) :=
    D_spec hX (K + 2) j (J hX j) (by omega)
      (by have := D_lt_J hX (K + 2); have := J_mono hX hk; omega)
  have hc : d (X (R hX (K + 2)) (J hX j)) (X (R hX j) (J hX j)) < e G (K + 2) + e G (K + 2) :=
    lt_of_le_of_lt (d_comm_le _ _) (hangman_lt hX hk (Nat.le_refl _))
  have hsum : d (X n j) (X (R hX j) (J hX j)) < e G K :=
    calc d (X n j) (X (R hX j) (J hX j))
        ≤ d (X n j) (X (R hX (K + 2)) j) + d (X (R hX (K + 2)) j) (X (R hX j) (J hX j)) :=
          d_triangle _ _ _
      _ ≤ d (X n j) (X (R hX (K + 2)) j)
          + (d (X (R hX (K + 2)) j) (X (R hX (K + 2)) (J hX j))
            + d (X (R hX (K + 2)) (J hX j)) (X (R hX j) (J hX j))) :=
          add_le_add_left (d_triangle _ _ _) _
      _ < e G (K + 2) + (e G (K + 2) + (e G (K + 2) + e G (K + 2))) :=
          add_lt_add ha (add_lt_add hb hc)
      _ ≐ (e G (K + 2) + e G (K + 2)) + (e G (K + 2) + e G (K + 2)) := (add_assoc _ _ _).symm
      _ ≤ e G K := e_quarter K
  calc δ - e G K ≤ (ε j - 0) - d (X n j) (X (R hX j) (J hX j)) :=
        sub_le_sub (hN₀ j (by omega)) (le_of_lt hsum)
    _ ≐ ε j - d (X n j) (X (R hX j) (J hX j)) := sub_congr (sub_zero _) .refl

end Construction

/-- **Theorem (completeness).** `(Q̄, d̄)` is complete: every `d̄`-Cauchy
sequence in `Q̄` converges in `Q̄` (with `ε` ranging over `Q̄`). -/
theorem complete (X : Nat → Qbar G) (hX : QbarCauchy X) : ∃ L : Qbar G, QbarLim X L :=
  ⟨diag hX, diag_lim hX⟩

end

end MyR
