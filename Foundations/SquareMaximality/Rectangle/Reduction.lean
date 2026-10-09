import SquareMaximality.Penalties

set_option autoImplicit false

/-!
# Reduction of the rectangular area penalty

This module formalizes the algebraic and telescoping part of the proof of the
rectangular area penalty in `general.tex`, Section 4.  The analytic and
determinantal ingredients are exposed individually in `AnalyticInputs`; in
particular, no theorem below assumes the final penalty itself.

The fields `matrixTreeLog` and `rectangularProductLog` are modular interfaces
for Matrix--Tree and the rectangular product formula; both are constructed
downstream.  The remaining fields correspond to the manuscript's
`C_a` error identity (equation `C-error`), hyperbolic increment formula
(`rectangular-increment`), residual estimates (`residual-bound`), and the two explicit
diagonal residual margins preceding equation `square-growth-summed`.
-/

namespace SquareMaximality.Rectangle

/-- A residual sum over the integer interval `[t,u)`. -/
def residualSum (R : ℕ → ℕ → ℝ) (a t u : ℕ) : ℝ :=
  ∑ v ∈ Finset.Ico t u, R a v

/-- Lower-level inputs used by the manuscript's proof of the rectangular penalty.

`logDeterminant` and `logProduct` keep Matrix--Tree and the product identity separate from the subsequent
hyperbolic calculation.  The constants `1/32` and `1/4` are retained explicitly so
that the strict `α` margins are visible in the interface. -/
structure AnalyticInputs (κ : ℝ) where
  C : ℕ → ℝ
  epsilon : ℕ → ℝ
  residual : ℕ → ℕ → ℝ
  alpha : ℝ
  logDeterminant : ℕ → ℕ → ℝ
  logProduct : ℕ → ℕ → ℝ
  /-- Matrix--Tree interface for this reduction layer. -/
  matrixTreeLog : ∀ {a t : ℕ}, 0 < a → 0 < t →
    Real.log (tauRect a t : ℝ) = logDeterminant a t
  /-- Rectangular determinant/product interface for this reduction layer. -/
  rectangularProductLog : ∀ {a t : ℕ}, 0 < a → 0 < t →
    logDeterminant a t = logProduct a t
  hyperbolicIncrement : ∀ {a t : ℕ}, 0 < a → 0 < t →
    logProduct a (t + 1) - logProduct a t = C a + residual a t
  cError : ∀ {a : ℕ}, 0 < a →
    C a = (a : ℝ) * κ - alpha - epsilon a
  epsilon_nonneg : ∀ {a : ℕ}, 0 < a → 0 ≤ epsilon a
  /-- Division-free form of `ε_a/a` being nonincreasing. -/
  epsilon_scaled_antitone : ∀ {a b : ℕ}, 0 < a → a ≤ b →
    (a : ℝ) * epsilon b ≤ (b : ℝ) * epsilon a
  residual_nonneg : ∀ {a t : ℕ}, 0 < a → 0 < t → 0 ≤ residual a t
  /-- The `K ≤ 1/32` part of equation `residual-bound`. -/
  residualInterval_lt_one_thirtysecond : ∀ {a t u : ℕ},
    0 < a → a ≤ t → t < u →
      residualSum residual a t u < (1 : ℝ) / 32
  one_thirtysecond_lt_alpha : (1 : ℝ) / 32 < alpha
  /-- The special residual `R_{a+1}(a) < 1/4` in the square-growth branch. -/
  secondDiagonalResidual_lt_quarter : ∀ {a : ℕ}, 0 < a →
    residual (a + 1) a < (1 : ℝ) / 4
  /-- The explicit margin `1/32 + 1/4 < 2α`. -/
  diagonalMargin : (1 : ℝ) / 32 + (1 : ℝ) / 4 < 2 * alpha

namespace AnalyticInputs

variable {κ : ℝ} (h : AnalyticInputs κ)

theorem alpha_pos : 0 < h.alpha := by
  linarith [h.one_thirtysecond_lt_alpha]

/-- The actual tree-count increment, obtained by composing the supplied
Matrix--Tree/product identity with the hyperbolic increment formula. -/
theorem log_increment {a t : ℕ} (ha : 0 < a) (ht : 0 < t) :
    Real.log (tauRect a (t + 1) : ℝ) - Real.log (tauRect a t : ℝ) =
      h.C a + h.residual a t := by
  rw [h.matrixTreeLog ha (by omega : 0 < t + 1),
    h.rectangularProductLog ha (by omega : 0 < t + 1),
    h.matrixTreeLog ha ht, h.rectangularProductLog ha ht]
  exact h.hyperbolicIncrement ha ht

theorem residualSum_nonneg {a t u : ℕ} (ha : 0 < a) (ht : 0 < t) :
    0 ≤ residualSum h.residual a t u := by
  apply Finset.sum_nonneg
  intro v hv
  rw [Finset.mem_Ico] at hv
  exact h.residual_nonneg ha (lt_of_lt_of_le ht hv.1)

theorem residualSum_lt_alpha {a t u : ℕ}
    (ha : 0 < a) (hat : a ≤ t) (htu : t < u) :
    residualSum h.residual a t u < h.alpha := by
  exact lt_trans (h.residualInterval_lt_one_thirtysecond ha hat htu)
    h.one_thirtysecond_lt_alpha

/-- Telescoping equation `rectangular-increment` over `[t,u)`. -/
theorem log_telescope {a t u : ℕ} (ha : 0 < a) (ht : 0 < t) (htu : t ≤ u) :
    Real.log (tauRect a u : ℝ) - Real.log (tauRect a t : ℝ) =
      ((u - t : ℕ) : ℝ) * h.C a + residualSum h.residual a t u := by
  induction u, htu using Nat.le_induction with
  | base => simp [residualSum]
  | succ u htu ih =>
      have hu : 0 < u := lt_of_lt_of_le ht htu
      calc
        Real.log (tauRect a (u + 1) : ℝ) - Real.log (tauRect a t : ℝ) =
            (Real.log (tauRect a (u + 1) : ℝ) - Real.log (tauRect a u : ℝ)) +
              (Real.log (tauRect a u : ℝ) - Real.log (tauRect a t : ℝ)) := by ring
        _ = (h.C a + h.residual a u) +
              (((u - t : ℕ) : ℝ) * h.C a + residualSum h.residual a t u) := by
              rw [h.log_increment ha hu, ih]
        _ = (((u + 1 - t : ℕ) : ℝ) * h.C a +
              residualSum h.residual a t (u + 1)) := by
              simp only [residualSum]
              rw [Finset.sum_Ico_succ_top htu]
              have : (u + 1 - t : ℕ) = (u - t) + 1 := by omega
              rw [this]
              push_cast
              ring

/-- The strict estimate in the manuscript's first branch, `r ≤ n ≤ s`.
This is the formal counterpart of equation `first-rectangle-telescope` and the
paragraph following it. -/
theorem first_branch_strict (h : AnalyticInputs κ) {n r s : ℕ}
    (hn : 0 < n) (hr : 0 < r) (hrs : r ≤ n) (hns : n ≤ s)
    (harea : n ^ 2 ≤ r * s) (hne : (r, s) ≠ (n, n)) :
    Real.log (tauRect r s : ℝ) - Real.log (tauRect n n : ℝ) <
      κ * ((r * s - n ^ 2 : ℕ) : ℝ) := by
  have hellk : n - r < s - n := by
    by_contra hnot
    have hle : s - n ≤ n - r := Nat.le_of_not_gt hnot
    have hsum : r + s ≤ 2 * n := by omega
    have hsumCast : (r : ℝ) + (s : ℝ) ≤ 2 * (n : ℝ) := by
      exact_mod_cast hsum
    have hsumR : 0 ≤ 2 * (n : ℝ) - (r : ℝ) - (s : ℝ) := by
      linarith
    have hareaR : (n : ℝ) ^ 2 ≤ (r : ℝ) * (s : ℝ) := by
      exact_mod_cast harea
    have hrEqR : (r : ℝ) = (n : ℝ) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ r by positivity) hsumR,
        sq_nonneg ((n : ℝ) - (r : ℝ))]
    have hrEq : r = n := by exact_mod_cast hrEqR
    have hsEq : s = n := by omega
    exact hne (by simp [hrEq, hsEq])
  have hnslt : n < s := by omega
  have hRS := log_telescope h hr hn hns
  have hRN := log_telescope h hn hr hrs
  have hdecomp :
      Real.log (tauRect r s : ℝ) - Real.log (tauRect n n : ℝ) =
        (((s - n : ℕ) : ℝ) * h.C r + residualSum h.residual r n s) -
          (((n - r : ℕ) : ℝ) * h.C n + residualSum h.residual n r n) := by
    calc
      Real.log (tauRect r s : ℝ) - Real.log (tauRect n n : ℝ) =
          (Real.log (tauRect r s : ℝ) - Real.log (tauRect r n : ℝ)) -
            (Real.log (tauRect n n : ℝ) - Real.log (tauRect n r : ℝ)) := by
              rw [tauRect_comm n r]
              ring
      _ = (((s - n : ℕ) : ℝ) * h.C r + residualSum h.residual r n s) -
            (((n - r : ℕ) : ℝ) * h.C n + residualSum h.residual n r n) := by
              rw [hRS, hRN]
  have hgapArea :
      ((n - r : ℕ) : ℝ) * (n : ℝ) ≤
        ((s - n : ℕ) : ℝ) * (r : ℝ) := by
    rw [Nat.cast_sub hrs, Nat.cast_sub hns]
    have hareaR : (n : ℝ) ^ 2 ≤ (r : ℝ) * (s : ℝ) := by
      exact_mod_cast harea
    nlinarith
  have hepsScale := h.epsilon_scaled_antitone hr hrs
  have hepsn := h.epsilon_nonneg hn
  have heps :
      ((n - r : ℕ) : ℝ) * h.epsilon n ≤
        ((s - n : ℕ) : ℝ) * h.epsilon r := by
    have h₁ := mul_le_mul_of_nonneg_left hepsScale
      (show (0 : ℝ) ≤ (s - n : ℕ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hgapArea hepsn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    apply le_of_mul_le_mul_left (a := (n : ℝ))
      (b := ((n - r : ℕ) : ℝ) * h.epsilon n)
      (c := ((s - n : ℕ) : ℝ) * h.epsilon r) _ hnR
    nlinarith
  have hresFirst := h.residualSum_lt_alpha hr hrs hnslt
  have hresSecond : 0 ≤ residualSum h.residual n r n :=
    residualSum_nonneg (u := n) h hn hr
  have hgapOne : (1 : ℝ) ≤ ((s - n : ℕ) : ℝ) - ((n - r : ℕ) : ℝ) := by
    have hgapCast : ((n - r : ℕ) : ℝ) + 1 ≤ ((s - n : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hellk)
    linarith
  have hmargin : h.alpha ≤
      (((s - n : ℕ) : ℝ) - ((n - r : ℕ) : ℝ)) * h.alpha := by
    simpa using mul_le_mul_of_nonneg_right hgapOne (le_of_lt h.alpha_pos)
  have hdelta :
      ((r * s - n ^ 2 : ℕ) : ℝ) =
        ((s - n : ℕ) : ℝ) * (r : ℝ) -
          ((n - r : ℕ) : ℝ) * (n : ℝ) := by
    rw [Nat.cast_sub harea, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_sub hns, Nat.cast_sub hrs]
    ring
  rw [hdecomp, h.cError hr, h.cError hn, hdelta]
  ring_nf at hmargin ⊢
  nlinarith

/-- One strict diagonal increment.  This packages exactly the calculation using
`R_a(a) < 1/32`, `R_{a+1}(a) < 1/4`, and `1/32 + 1/4 < 2α`. -/
theorem diagonal_step_strict (h : AnalyticInputs κ) {a : ℕ} (ha : 0 < a) :
    Real.log (tauRect (a + 1) (a + 1) : ℝ) -
        Real.log (tauRect a a : ℝ) <
      (2 * (a : ℝ) + 1) * κ := by
  have h₁ := h.log_increment ha ha
  have h₂ := h.log_increment (by omega : 0 < a + 1) ha
  have hres₁ := h.residualInterval_lt_one_thirtysecond ha (le_refl a)
    (by omega : a < a + 1)
  simp [residualSum] at hres₁
  have hres₂ := h.secondDiagonalResidual_lt_quarter ha
  have heps₁ := h.epsilon_nonneg ha
  have heps₂ := h.epsilon_nonneg (by omega : 0 < a + 1)
  calc
    Real.log (tauRect (a + 1) (a + 1) : ℝ) -
        Real.log (tauRect a a : ℝ) =
      (Real.log (tauRect (a + 1) (a + 1) : ℝ) -
          Real.log (tauRect (a + 1) a : ℝ)) +
        (Real.log (tauRect a (a + 1) : ℝ) -
          Real.log (tauRect a a : ℝ)) := by
            rw [tauRect_comm (a + 1) a]
            ring
    _ = (h.C (a + 1) + h.residual (a + 1) a) +
          (h.C a + h.residual a a) := by rw [h₂, h₁]
    _ < (2 * (a : ℝ) + 1) * κ := by
      rw [h.cError (by omega : 0 < a + 1), h.cError ha]
      push_cast
      nlinarith [h.diagonalMargin]

/-- Non-strict telescoped square growth.  Every nontrivial instance is in fact strict;
the separate strict lemma below records that endpoint. -/
theorem square_growth_le (h : AnalyticInputs κ) {n r : ℕ} (hn : 0 < n) (hnr : n ≤ r) :
    Real.log (tauRect r r : ℝ) - Real.log (tauRect n n : ℝ) ≤
      κ * ((r : ℝ) ^ 2 - (n : ℝ) ^ 2) := by
  induction r, hnr using Nat.le_induction with
  | base => simp
  | succ r hnr ih =>
      have hr : 0 < r := lt_of_lt_of_le hn hnr
      have hstep := h.diagonal_step_strict hr
      calc
        Real.log (tauRect (r + 1) (r + 1) : ℝ) -
            Real.log (tauRect n n : ℝ) =
          (Real.log (tauRect (r + 1) (r + 1) : ℝ) -
              Real.log (tauRect r r : ℝ)) +
            (Real.log (tauRect r r : ℝ) - Real.log (tauRect n n : ℝ)) := by ring
        _ ≤ (2 * (r : ℝ) + 1) * κ +
              κ * ((r : ℝ) ^ 2 - (n : ℝ) ^ 2) :=
                add_le_add (le_of_lt hstep) ih
        _ = κ * (((r + 1 : ℕ) : ℝ) ^ 2 - (n : ℝ) ^ 2) := by
              push_cast
              ring

/-- Strict version of equation `square-growth-summed`. -/
theorem square_growth_strict (h : AnalyticInputs κ) {n r : ℕ}
    (hn : 0 < n) (hnr : n < r) :
    Real.log (tauRect r r : ℝ) - Real.log (tauRect n n : ℝ) <
      κ * ((r : ℝ) ^ 2 - (n : ℝ) ^ 2) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have hnr' : n ≤ r := by omega
  have hprev := h.square_growth_le hn hnr'
  have hr : 0 < r := lt_of_lt_of_le hn hnr'
  have hstep := h.diagonal_step_strict hr
  calc
    Real.log (tauRect (r + 1) (r + 1) : ℝ) -
        Real.log (tauRect n n : ℝ) =
      (Real.log (tauRect (r + 1) (r + 1) : ℝ) -
          Real.log (tauRect r r : ℝ)) +
        (Real.log (tauRect r r : ℝ) - Real.log (tauRect n n : ℝ)) := by ring
    _ < (2 * (r : ℝ) + 1) * κ +
          κ * ((r : ℝ) ^ 2 - (n : ℝ) ^ 2) := add_lt_add_of_lt_of_le hstep hprev
    _ = κ * (((r + 1 : ℕ) : ℝ) ^ 2 - (n : ℝ) ^ 2) := by
          push_cast
          ring

/-- Strict version of equation `rectangle-extension` for `r < s`. -/
theorem rectangle_extension_strict (h : AnalyticInputs κ) {r s : ℕ}
    (hr : 0 < r) (hrs : r < s) :
    Real.log (tauRect r s : ℝ) - Real.log (tauRect r r : ℝ) <
      κ * (r : ℝ) * ((s - r : ℕ) : ℝ) := by
  have htel := h.log_telescope hr hr (Nat.le_of_lt hrs)
  have hres := h.residualSum_lt_alpha hr (le_refl r) hrs
  have heps := h.epsilon_nonneg hr
  have hgap : (1 : ℝ) ≤ ((s - r : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hrs))
  have hmargin : h.alpha ≤ ((s - r : ℕ) : ℝ) * h.alpha := by
    simpa using mul_le_mul_of_nonneg_right hgap (le_of_lt h.alpha_pos)
  rw [htel, h.cError hr]
  ring_nf at hmargin ⊢
  nlinarith

/-- Non-strict rectangle extension, including the zero-length case `s = r`. -/
theorem rectangle_extension_le (h : AnalyticInputs κ) {r s : ℕ}
    (hr : 0 < r) (hrs : r ≤ s) :
    Real.log (tauRect r s : ℝ) - Real.log (tauRect r r : ℝ) ≤
      κ * (r : ℝ) * ((s - r : ℕ) : ℝ) := by
  rcases eq_or_lt_of_le hrs with rfl | hrs
  · simp
  · exact le_of_lt (h.rectangle_extension_strict hr hrs)

/-- The strict estimate in the manuscript's second branch, `n ≤ r ≤ s`. -/
theorem second_branch_strict (h : AnalyticInputs κ) {n r s : ℕ}
    (hn : 0 < n) (hnr : n ≤ r) (hrs : r ≤ s)
    (harea : n ^ 2 ≤ r * s) (hne : (r, s) ≠ (n, n)) :
    Real.log (tauRect r s : ℝ) - Real.log (tauRect n n : ℝ) <
      κ * ((r * s - n ^ 2 : ℕ) : ℝ) := by
  have hr : 0 < r := lt_of_lt_of_le hn hnr
  have hdelta :
      ((r * s - n ^ 2 : ℕ) : ℝ) =
        ((r : ℝ) ^ 2 - (n : ℝ) ^ 2) +
          (r : ℝ) * ((s - r : ℕ) : ℝ) := by
    rw [Nat.cast_sub harea, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hrs]
    ring
  by_cases hrn : r = n
  · subst r
    have hns : n < s := by
      apply lt_of_le_of_ne hrs
      intro hsn
      apply hne
      simp [hsn]
    have hext := h.rectangle_extension_strict hn hns
    rw [hdelta]
    simpa [mul_assoc] using hext
  · have hnrlt : n < r := lt_of_le_of_ne hnr (Ne.symm hrn)
    have hsquare := h.square_growth_strict hn hnrlt
    have hext := h.rectangle_extension_le hr hrs
    calc
      Real.log (tauRect r s : ℝ) - Real.log (tauRect n n : ℝ) =
          (Real.log (tauRect r r : ℝ) - Real.log (tauRect n n : ℝ)) +
            (Real.log (tauRect r s : ℝ) - Real.log (tauRect r r : ℝ)) := by ring
      _ < κ * ((r : ℝ) ^ 2 - (n : ℝ) ^ 2) +
            κ * (r : ℝ) * ((s - r : ℕ) : ℝ) :=
              add_lt_add_of_lt_of_le hsquare hext
      _ = κ * ((r * s - n ^ 2 : ℕ) : ℝ) := by rw [hdelta]; ring

/-- The lower-level data prove the manuscript's complete strict rectangular
area penalty, including both order branches. -/
theorem strictRectangularAreaPenalty_of_analyticInputs
    (h : AnalyticInputs κ) : StrictRectangularAreaPenalty κ := by
  intro n r s hn hr hs hrs harea hne
  rcases le_total r n with hrn | hnr
  · have hns : n ≤ s := by
      by_contra hnot
      have hsn : s < n := Nat.lt_of_not_ge hnot
      have hrsn : r < n := lt_of_le_of_lt hrs hsn
      have hprod : r * s < n * n := by
        nlinarith
      exact (not_lt_of_ge harea) (by simpa [pow_two] using hprod)
    exact h.first_branch_strict hn hr hrn hns harea hne
  · exact h.second_branch_strict hn hnr hrs harea hne

/-- The corresponding non-strict rectangular area penalty.  At `(r,s)=(n,n)`
both sides are definitionally zero; all other cases use the strict theorem. -/
theorem rectangularAreaPenalty_of_analyticInputs
    (h : AnalyticInputs κ) : RectangularAreaPenalty κ := by
  intro n r s hn hr hs hrs harea
  by_cases heq : (r, s) = (n, n)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    simp [pow_two]
  · exact le_of_lt
      (h.strictRectangularAreaPenalty_of_analyticInputs hn hr hs hrs harea heq)

end AnalyticInputs

end SquareMaximality.Rectangle
