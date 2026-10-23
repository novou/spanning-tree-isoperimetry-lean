module

public import SpanningTreeIsoperimetry.PositiveFrequencyExponential
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

@[expose] public section

/-! Direct weighted coefficient estimates needed for the triangular
exponential. There is no new Banach algebra instance. -/
namespace SpanningTreeIsoperimetry.WeightedPowerSeries
open PowerSeries PositiveFrequencyExponential
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def term (p : PowerSeries ℝ) (n : ℕ) : ℝ := (1+(n : ℝ))*|PowerSeries.coeff n p|
abbrev SummableWeighted (p : PowerSeries ℝ) : Prop := Summable (term p)
def mass (p : PowerSeries ℝ) : ℝ := ∑' n,term p n

theorem term_nonneg (p : PowerSeries ℝ) (n : ℕ) : 0≤term p n := by unfold term; positivity
theorem mass_nonneg (p : PowerSeries ℝ) : 0≤mass p := tsum_nonneg (term_nonneg p)


theorem abs_coefficient_le_term (p : PowerSeries ℝ) (n : ℕ) :
    |PowerSeries.coeff n p|≤term p n := by
  unfold term
  exact le_mul_of_one_le_left (abs_nonneg _) (by linarith [Nat.cast_nonneg (α := ℝ) n])

theorem coefficients_summable {p : PowerSeries ℝ} (hp : SummableWeighted p) :
    Summable (fun n => |PowerSeries.coeff n p|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (abs_coefficient_le_term p) hp

theorem coefficients_mass_le {p : PowerSeries ℝ} (hp : SummableWeighted p) :
    (∑' n,|PowerSeries.coeff n p|)≤mass p :=
  (coefficients_summable hp).tsum_le_tsum (abs_coefficient_le_term p) hp

theorem term_one (n : ℕ) : term (1 : PowerSeries ℝ) n=if n=0 then 1 else 0 := by
  by_cases hn : n=0 <;> simp [term,PowerSeries.coeff_one,hn]

theorem one_summable : SummableWeighted (1 : PowerSeries ℝ) := by
  change Summable (fun n => term (1 : PowerSeries ℝ) n)
  simpa only [term_one] using (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).summable

theorem mass_one : mass (1 : PowerSeries ℝ)=1 := by simp [mass,term_one]

theorem term_mul_le (p q : PowerSeries ℝ) (n : ℕ) :
    term (p*q) n≤∑ a∈Finset.antidiagonal n,term p a.1*term q a.2 := by
  rw [term,PowerSeries.coeff_mul]
  calc
    (1+(n : ℝ))*|∑ a∈Finset.antidiagonal n,PowerSeries.coeff a.1 p*PowerSeries.coeff a.2 q|
        ≤(1+(n : ℝ))*(∑ a∈Finset.antidiagonal n,|PowerSeries.coeff a.1 p*PowerSeries.coeff a.2 q|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _=∑ a∈Finset.antidiagonal n,(1+(n : ℝ))*|PowerSeries.coeff a.1 p*PowerSeries.coeff a.2 q| := by rw [Finset.mul_sum]
    _≤∑ a∈Finset.antidiagonal n,term p a.1*term q a.2 := by
      apply Finset.sum_le_sum
      intro a ha
      have hn : (n : ℝ)=(a.1 : ℝ)+a.2 := by exact_mod_cast (Finset.mem_antidiagonal.mp ha).symm
      have hw : 1+(n : ℝ)≤(1+(a.1 : ℝ))*(1+(a.2 : ℝ)) := by
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) a.1) (Nat.cast_nonneg (α := ℝ) a.2)]
      rw [abs_mul]
      calc
        _≤((1+(a.1 : ℝ))*(1+(a.2 : ℝ)))*(|PowerSeries.coeff a.1 p| * |PowerSeries.coeff a.2 q|) :=
          mul_le_mul_of_nonneg_right hw (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _=term p a.1*term q a.2 := by unfold term; ring

theorem mul_summable {p q : PowerSeries ℝ} (hp : SummableWeighted p) (hq : SummableWeighted q) :
    SummableWeighted (p*q) := by
  have hpair := hp.mul_of_nonneg hq (term_nonneg p) (term_nonneg q)
  have hsum := summable_sum_mul_antidiagonal_of_summable_mul hpair
  exact Summable.of_nonneg_of_le (term_nonneg _) (term_mul_le p q) hsum

theorem mass_mul_le {p q : PowerSeries ℝ} (hp : SummableWeighted p) (hq : SummableWeighted q) :
    mass (p*q)≤mass p*mass q := by
  let f : ℕ → ℝ := term p
  let g : ℕ → ℝ := term q
  have hf : Summable f := hp
  have hg : Summable g := hq
  have hpair : Summable (fun a : ℕ×ℕ => f a.1*g a.2) :=
    hf.mul_of_nonneg hg (term_nonneg p) (term_nonneg q)
  have hsum := summable_sum_mul_antidiagonal_of_summable_mul hpair
  have hb := (mul_summable hp hq).tsum_le_tsum (term_mul_le p q) hsum
  have he : (∑' n,∑ a∈Finset.antidiagonal n,f a.1*g a.2)=mass p*mass q := by
    exact (hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hpair).symm
  exact hb.trans_eq he

theorem pow_control {p : PowerSeries ℝ} (hp : SummableWeighted p) (m : ℕ) :
    SummableWeighted (p^m) ∧ mass (p^m)≤(mass p)^m := by
  induction m with
  | zero => simp only [pow_zero,mass_one,le_refl,and_true]; exact one_summable
  | succ m ih =>
    constructor
    · rw [pow_succ]
      exact mul_summable ih.1 hp
    · rw [pow_succ]
      exact (mass_mul_le ih.1 hp).trans
        (by simpa only [pow_succ] using mul_le_mul_of_nonneg_right ih.2 (mass_nonneg p))

private theorem term_subst_le {p q : PowerSeries ℝ} (hp0 : p.constantCoeff=0) (n : ℕ) :
    term (q.subst p) n≤∑ m∈Finset.range (n+1),|PowerSeries.coeff m q| * term (p^m) n := by
  rw [term,coefficient_substitution hp0]
  calc
    _≤(1+(n : ℝ))*(∑ m∈Finset.range (n+1),|PowerSeries.coeff m q*PowerSeries.coeff n (p^m)|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _=∑ m∈Finset.range (n+1),|PowerSeries.coeff m q| * term (p^m) n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [abs_mul]
      unfold term
      ring

/-- The common majorant mechanism used for both the exponential and its
second-order remainder. Its series hypothesis is discharged in those uses. -/
theorem subst_control {p q : PowerSeries ℝ} (hp0 : p.constantCoeff=0)
    (hp : SummableWeighted p)
    (hq : Summable (fun m => |PowerSeries.coeff m q| * (mass p)^m)) :
    SummableWeighted (q.subst p) ∧ mass (q.subst p)≤∑' m,|PowerSeries.coeff m q| * (mass p)^m := by
  let F : ℕ×ℕ → ℝ := fun a => |PowerSeries.coeff a.1 q| * term (p^a.1) a.2
  have hF0 (a : ℕ×ℕ) : 0≤F a := mul_nonneg (abs_nonneg _) (term_nonneg _ _)
  have hFn (m : ℕ) : Summable (fun n => F (m,n)) := (pow_control hp m).1.mul_left |PowerSeries.coeff m q|
  have hFe (m : ℕ) : (∑' n,F (m,n))=|PowerSeries.coeff m q| * mass (p^m) := by
    dsimp only [F,mass]
    convert! (pow_control hp m).1.tsum_mul_left |PowerSeries.coeff m q| using 1
  have hFm : Summable (fun m => ∑' n,F (m,n)) := by
    simp_rw [hFe]
    exact Summable.of_nonneg_of_le (fun m => mul_nonneg (abs_nonneg _) (mass_nonneg _))
      (fun m => mul_le_mul_of_nonneg_left (pow_control hp m).2 (abs_nonneg _)) hq
  have hF : Summable F := (summable_prod_of_nonneg hF0).mpr ⟨hFn,hFm⟩
  have hb (n : ℕ) : term (q.subst p) n≤∑' m,F (m,n) := by
    apply (term_subst_le hp0 n).trans
    exact hF.prod_symm.prod_factor n |>.sum_le_tsum (Finset.range (n+1)) (fun m _ => hF0 (m,n))
  have hsub : SummableWeighted (q.subst p) :=
    Summable.of_nonneg_of_le (term_nonneg _) hb hF.prod_symm.prod
  refine ⟨hsub,?_⟩
  have hbound := hsub.tsum_le_tsum hb hF.prod_symm.prod
  have he : (∑' n,∑' m,F (m,n))=(∑' m,|PowerSeries.coeff m q| * mass (p^m)) := by
    rw [hF.tsum_comm]
    exact tsum_congr hFe
  apply (hbound.trans_eq he).trans
  exact hFm.congr hFe |>.tsum_le_tsum
    (fun m => mul_le_mul_of_nonneg_left (pow_control hp m).2 (abs_nonneg _)) hq

end
end SpanningTreeIsoperimetry.WeightedPowerSeries
