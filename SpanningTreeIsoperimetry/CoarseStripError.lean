import SpanningTreeIsoperimetry.FluxBounds
import SpanningTreeIsoperimetry.FiniteLongStripError
import SpanningTreeIsoperimetry.RefinedEntropyBounds

/-! The first (reciprocal-square) finite-strip estimate of Section 4.
The proof uses the checked fourth-order Green bound away from the terminal
strip and the total closed-word mass at that endpoint. -/
namespace SpanningTreeIsoperimetry.CoarseStripError
open Ferrers CornerEnergy CornerStripBridge FluxBounds FiniteStripError
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem cubic_ratio_le {q k d : ℝ} (hq : 0<q) (hk : 1≤k)
    (hd : 2*q*k≤d) : (cubic k/3)/d^2≤k/(2*q^2) := by
  have hk0 : 0<k := by linarith
  have hden : 0<2*q*k := by positivity
  have hc : cubic k/3≤2*k^3 := by
    unfold cubic
    have h := mul_le_mul_of_nonneg_left
      (mul_le_mul (show k+1≤2*k by linarith) (show 2*k+1≤3*k by linarith)
        (by positivity : 0≤2*k+1) (by positivity : 0≤2*k)) hk0.le
    nlinarith only [h]
  calc
    (cubic k/3)/d^2≤(2*k^3)/(2*q*k)^2 := by
      apply div_le_div₀ (by positivity) hc (sq_pos_of_pos hden)
      exact pow_le_pow_left₀ hden.le hd 2
    _=k/(2*q^2) := by field_simp [hq.ne',hk0.ne'] <;> ring

private theorem quadratic_ratio_le {q k d : ℝ} (hq : 0<q) (hk : 1≤k)
    (hd : q*(k+1)≤d) : quadratic k/d^2≤k/(2*q^2) := by
  have hk0 : 0<k := by linarith
  have hden : 0<q*(k+1) := by positivity
  calc
    quadratic k/d^2≤quadratic k/(q*(k+1))^2 := by
      exact div_le_div_of_nonneg_left (by unfold quadratic; positivity)
        (sq_pos_of_pos hden) (pow_le_pow_left₀ hden.le hd 2)
    _=k/(q^2*(k+1)) := by
      unfold quadratic
      field_simp [hq.ne',hk0.ne',ne_of_gt (show 0<k+1 by positivity)]
      <;> ring
    _≤k/(2*q^2) := by
      apply div_le_div_of_nonneg_left hk0.le (by positivity)
      nlinarith [mul_nonneg (sq_nonneg q) (show 0≤k-1 by linarith)]

/-- A uniform conversion from the fourth-order flux envelope to a coarser
reciprocal-square estimate. No integer hypothesis is needed. -/
theorem square_flux_le {r k : ℝ} (hk : 1≤k) (hr : k+2≤r) :
    fluxBound r r k≤Real.pi^3*k/(30*(r-k)^2) := by
  let q := r-k
  have hq : 2≤q := by dsimp [q]; linarith
  have hq0 : 0<q := by linarith
  have hk0 : 0≤k := by linarith
  have heq : r=q+k := by dsimp [q]; ring
  have h4 : 2*q*k≤r^2-4 := by rw [heq]; nlinarith [sq_nonneg k]
  have hk2 : 2*q*k≤r^2-k^2 := by rw [heq]; nlinarith [sq_nonneg q]
  have h1 : q*(k+1)≤r^2-1 := by
    rw [heq]
    nlinarith [mul_nonneg (show 0≤q by linarith) (show 0≤k-1 by linarith),sq_nonneg k]
  have hk1 : q*(k+1)≤r^2-(k+1)^2 := by
    rw [heq]
    nlinarith [mul_nonneg (show 0≤q-2 by linarith) hk0]
  have a := cubic_ratio_le hq0 hk h4
  have b := cubic_ratio_le hq0 hk hk2
  have c := quadratic_ratio_le hq0 hk h1
  have d := quadratic_ratio_le hq0 hk hk1
  have hsum : (cubic k/3)*(1/(r^2-4)^2+1/(r^2-k^2)^2)+
      quadratic k*(1/(r^2-1)^2+1/(r^2-(k+1)^2)^2)≤2*k/q^2 := by
    simp only [mul_add,mul_one_div] at ⊢
    rw [show 2*k/q^2=4*(k/(2*q^2)) by ring]
    linarith only [a,b,c,d]
  calc
    fluxBound r r k≤Real.pi^3/60*(2*k/q^2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _=Real.pi^3*k/(30*(r-k)^2) := by dsimp [q]; simp only [div_eq_mul_inv,mul_inv_rev]; ring

theorem flux_le_coarse {r s k : ℝ} (hk : 1≤k) (hr : k+2≤r) (hrs : r≤s) :
    fluxBound r s k≤4*k/(Real.pi*(r-k)^2) ∧
    fluxBound s r k≤4*k/(Real.pi*(r-k)^2) := by
  have hr2 : 2<r := by linarith
  have hkr : k+1<r := by linarith
  have hbase := square_flux_le hk hr
  have hpi2 : Real.pi^2<10 := by
    nlinarith [mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d2]
  have hpi4 : Real.pi^4<100 := by
    have h := mul_pos (sub_pos.mpr hpi2)
      (show 0<10+Real.pi^2 by positivity)
    nlinarith only [h]
  have hcoeff : Real.pi^3/30≤4/Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    nlinarith only [hpi4]
  have hbound : Real.pi^3*k/(30*(r-k)^2)≤4*k/(Real.pi*(r-k)^2) := by
    have h := mul_le_mul_of_nonneg_right hcoeff (show 0≤k/(r-k)^2 by positivity)
    convert h using 1 <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring
  exact ⟨(fluxBound_antitone_right (by linarith) hkr hrs).trans (hbase.trans hbound),
    (fluxBound_antitone_left hr2 hrs (by linarith)).trans (hbase.trans hbound)⟩

/-- The total normalized closed-word weight bounds every finite correction. -/
theorem correction_le_total (U M : Diagram) :
    correction U M≤(M.card : ℝ)*(Real.log 4-SquareMaximality.squareLatticeEntropy) := by
  have h := (correctionTerm_summable U M).tsum_le_tsum
    (correctionTerm_le_closedWordTerm U M) (closedWordTerm_summable.mul_left (M.card : ℝ))
  simpa only [correction,tsum_mul_left,closedWordTerm_hasSum.tsum_eq] using h

theorem correction_le_card (U M : Diagram) : correction U M≤M.card := by
  have hlog : Real.log 4<2 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ)<2) (by norm_num : (2 : ℝ)≠1)
    have he : Real.log 4=2*Real.log 2 := by
      rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]
      norm_num
    linarith
  have hmass : Real.log 4-SquareMaximality.squareLatticeEntropy≤1 := by
    linarith [RefinedEntropyBounds.entropy_lower]
  exact (correction_le_total U M).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg (α := ℝ) M.card))

theorem correction_transpose (U M : Diagram) :
    correction (transpose U) (transpose M)=correction U M := by
  apply tsum_congr
  intro n
  have hs : lostSum (transpose U) (transpose M) (n+1)=lostSum U M (n+1) := by
    unfold lostSum
    rw [← (swapClosedWordEquiv (n+1)).sum_comp]
    apply Finset.sum_congr rfl
    intro w _
    change lostCount (transpose U) (transpose M) (normalizedVisited (swapWord w.val))=_
    rw [normalizedVisited_swapWord,lostCount_transpose]
  simp only [correctionTerm,hs]

/-- The fourth-order theorem rewritten in primal coordinates and the actual
closed-word correction. -/
theorem vertical_correction_le_flux {r s k : ℕ} (hr : 3≤r) (hk : 1≤k) (hs : k+1<s) :
    correction (faceRectangle (r-1) (s-1)) (verticalDiagram k)≤fluxBound r s k := by
  have h := (FiniteLongStripError.finite_long_strip_error (R := r-1) (S := s-1)
    (by omega) (k-1) (by omega)).2
  have hkk : k-1+1=k := by omega
  have hrr : ((r-1 : ℕ) : ℝ)+1=(r : ℝ) := by exact_mod_cast (show r-1+1=r by omega)
  have hss : ((s-1 : ℕ) : ℝ)+1=(s : ℝ) := by exact_mod_cast (show s-1+1=s by omega)
  have hkr : ((k-1 : ℕ) : ℝ)+1=(k : ℝ) := by exact_mod_cast hkk
  simp only [hkk,hrr,hss,hkr] at h
  rw [dirichletEnergy_eq (verticalDiagram_ferrers k),verticalDiagram_energy] at h
  linarith only [h]

theorem horizontal_correction_le_flux {r s k : ℕ} (hs : 3≤s) (hk : 1≤k) (hr : k+1<r) :
    correction (faceRectangle (r-1) (s-1)) (horizontalStrip k)≤fluxBound s r k := by
  have h := vertical_correction_le_flux hs hk hr
  rw [verticalDiagram_transpose] at h
  have he := correction_transpose (faceRectangle (r-1) (s-1)) (horizontalStrip k)
  rw [transpose_faceRectangle] at he
  rwa [he] at h

/-- Exactly the first upper bound in `lem:finite-strip-error`. -/
def coarseBound (r s k : ℝ) : ℝ := 4*k/Real.pi*(1/(r-k)^2+1/(s-1)^2)

theorem coarseBound_ge_first {r s k : ℝ} (hk : 0≤k) :
    4*k/(Real.pi*(r-k)^2)≤coarseBound r s k := by
  have ht : 0≤4*k/Real.pi*(1/(s-1)^2) := by positivity
  unfold coarseBound
  convert le_add_of_nonneg_right ht using 1 <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring

theorem correction_both_le {r s k : ℕ} (hr : 2≤r) (hrs : r≤s) (hk : k<r) :
    correction (faceRectangle (r-1) (s-1)) (horizontalStrip k)≤coarseBound r s k ∧
    correction (faceRectangle (r-1) (s-1)) (verticalDiagram k)≤coarseBound r s k := by
  by_cases hk0 : k=0
  · subst k
    simp [horizontalStrip,verticalDiagram,correction_empty,coarseBound]
  have hk1 : 1≤k := by omega
  by_cases hclear : k+2≤r
  · have hf := flux_le_coarse (by exact_mod_cast hk1 : (1 : ℝ)≤k)
      (by exact_mod_cast hclear : (k : ℝ)+2≤r) (by exact_mod_cast hrs : (r : ℝ)≤s)
    have hc := coarseBound_ge_first (r := (r : ℝ)) (s := (s : ℝ)) (Nat.cast_nonneg (α := ℝ) k)
    exact ⟨(horizontal_correction_le_flux (by omega) hk1 (by omega)).trans (hf.2.trans hc),
      (vertical_correction_le_flux (by omega) hk1 (by omega)).trans (hf.1.trans hc)⟩
  · have hgap : (r : ℝ)-(k : ℝ)=1 := by
      have h : r=k+1 := by omega
      exact_mod_cast (show (r : ℤ)-(k : ℤ)=1 by omega)
    have hpi : Real.pi≤4 := Real.pi_lt_four.le
    have hfirst : (k : ℝ)≤4*k/(Real.pi*((r : ℝ)-k)^2) := by
      rw [hgap]
      simp only [one_pow,mul_one]
      apply (le_div_iff₀ Real.pi_pos).mpr
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (sub_nonneg.mpr hpi)]
    have hb : (k : ℝ)≤coarseBound r s k := hfirst.trans (coarseBound_ge_first (Nat.cast_nonneg k))
    constructor
    · exact (correction_le_card _ _).trans (by simpa only [card_horizontalStrip] using hb)
    · exact (correction_le_card _ _).trans (by
        simpa only [verticalDiagram_transpose,card_transpose,card_horizontalStrip] using hb)

/-- The actual finite Dirichlet-energy error for either orientation of a
corner strip, including the empty strip. Side lengths are primal lengths. -/
theorem finite_strip_error {r s k : ℕ} (hr : 2≤r) (hrs : r≤s) (hk : k<r)
    {M : Diagram} (hM : M=horizontalStrip k ∨ M=verticalDiagram k)
    (hfit : M⊆faceRectangle (r-1) (s-1)) :
    0≤dirichletEnergy hfit-realEnergy (horizontalStrip k) ∧
    dirichletEnergy hfit-realEnergy (horizontalStrip k)≤
      4*(k : ℝ)/Real.pi*(1/((r : ℝ)-k)^2+1/((s : ℝ)-1)^2) := by
  obtain ⟨hh,hv⟩ := correction_both_le hr hrs hk
  rcases hM with rfl|rfl
  · rw [dirichletEnergy_eq (horizontalStrip_isFerrers k)]
    constructor
    · linarith [correction_nonneg (faceRectangle (r-1) (s-1)) (horizontalStrip k)]
    · change _≤coarseBound r s k
      linarith only [hh]
  · rw [dirichletEnergy_eq (verticalDiagram_ferrers k),verticalDiagram_energy]
    constructor
    · linarith [correction_nonneg (faceRectangle (r-1) (s-1)) (verticalDiagram k)]
    · change _≤coarseBound r s k
      linarith only [hv]

/-- The empty-strip clause also includes primal side length one. -/
theorem finite_empty_strip_error {r s : ℕ}
    (hfit : horizontalStrip 0⊆faceRectangle (r-1) (s-1)) :
    dirichletEnergy hfit-realEnergy (horizontalStrip 0)=0 := by
  rw [dirichletEnergy_eq (horizontalStrip_isFerrers 0)]
  simp [horizontalStrip,correction_empty]

end
end SpanningTreeIsoperimetry.CoarseStripError
