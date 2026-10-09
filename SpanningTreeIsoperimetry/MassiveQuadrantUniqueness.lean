import SpanningTreeIsoperimetry.RegularizedQuadrantGreen

/-! Bounded uniqueness for z>4 by the strict factor 4/z.
The final endpoint identifies bounded Poisson solutions with the actual
finite-box exhaustion, rather than defining Green entries by a candidate. -/
namespace SpanningTreeIsoperimetry.MassiveQuadrantUniqueness
open Ferrers BoundaryGreenBounds RegularizedQuadrantGreen Filter
open scoped Topology
noncomputable section

theorem contraction_bound {z B : ℝ} (hz : 4<z) (hB : 0≤B) (f : Point → ℝ)
    (hf : ∀ p,laplacianZ z f p=0) (hb : ∀ p,|f p|≤B) (p : Point) :
    |f p|≤(4/z)*B := by
  have hz0 : 0<z := by linarith
  have he := abs_le.mp (hb (p.1+1,p.2))
  have hn := abs_le.mp (hb (p.1,p.2+1))
  have hw : -B≤(if p.1=0 then 0 else f (p.1-1,p.2)) ∧
      (if p.1=0 then 0 else f (p.1-1,p.2))≤B := by
    split_ifs
    · constructor <;> linarith
    · exact abs_le.mp (hb (p.1-1,p.2))
  have hs : -B≤(if p.2=0 then 0 else f (p.1,p.2-1)) ∧
      (if p.2=0 then 0 else f (p.1,p.2-1))≤B := by
    split_ifs
    · constructor <;> linarith
    · exact abs_le.mp (hb (p.1,p.2-1))
  have hp := hf p
  rw [laplacianZ_explicit] at hp
  have hu : f p*z≤4*B := by linarith [he.2,hn.2,hw.2,hs.2]
  have hl : -4*B≤f p*z := by linarith [he.1,hn.1,hw.1,hs.1]
  have hupper : f p≤4*B/z := (le_div_iff₀ hz0).mpr hu
  have hlower : -(4*B/z)≤f p := by
    rw [← neg_div]
    apply (div_le_iff₀ hz0).mpr
    linarith only [hl]
  have h := abs_le.mpr ⟨hlower,hupper⟩
  convert h using 1 <;> ring

theorem iterated_bound {z C : ℝ} (hz : 4<z) (hC : 0≤C) (f : Point → ℝ)
    (hf : ∀ p,laplacianZ z f p=0) (hb : ∀ p,|f p|≤C) (n : ℕ) (p : Point) :
    |f p|≤C*(4/z)^n := by
  have hz0 : 0<z := by linarith
  induction n generalizing p with
  | zero => simpa only [pow_zero,mul_one] using hb p
  | succ n ih =>
    have h := contraction_bound hz (show 0≤C*(4/z)^n by positivity) f hf (fun p => ih p) p
    convert h using 1 <;> rw [pow_succ] <;> ring

theorem bounded_harmonic_eq_zero {z C : ℝ} (hz : 4<z) (hC : 0≤C) (f : Point → ℝ)
    (hf : ∀ p,laplacianZ z f p=0) (hb : ∀ p,|f p|≤C) (p : Point) : f p=0 := by
  have hz0 : 0<z := by linarith
  have hq0 : (0 : ℝ)≤4/z := by positivity
  have hq1 : (4 : ℝ)/z<1 := (div_lt_one hz0).mpr hz
  have ht : Tendsto (fun n : ℕ => C*(4/z)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
  have hzero : |f p|≤0 := ge_of_tendsto ht
    (Filter.Eventually.of_forall (fun n => iterated_bound hz hC f hf hb n p))
  exact abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))

/-- Identification with the actual regularized quadrant inverse. -/
theorem eq_quadrantGreenZ_of_bounded_poisson {z C : ℝ} (hz : 4<z) (hC : 0≤C)
    (q : Point) (f : Point → ℝ) (hb : ∀ p,|f p|≤C)
    (hf : ∀ p,laplacianZ z f p=if p=q then 1 else 0) (p : Point) :
    f p=quadrantGreenZ z p q := by
  have hden : 0<z-4 := by linarith
  have hg (t : Point) : |quadrantGreenZ z t q|≤1/(z-4) := by
    rw [abs_of_nonneg (quadrantGreenZ_nonneg hz.le t q)]
    exact quadrantGreenZ_uniform_bound hz t q
  have hbound (t : Point) : |f t-quadrantGreenZ z t q|≤C+1/(z-4) := by
    have h := abs_sub_le (f t) (0 : ℝ) (quadrantGreenZ z t q)
    simp only [sub_zero,zero_sub,abs_neg] at h
    linarith [hb t,hg t]
  have hpoisson (t : Point) : laplacianZ z (fun x => f x-quadrantGreenZ z x q) t=0 := by
    rw [laplacianZ_sub,hf t,quadrantGreenZ_equation hz.le,sub_self]
  have h := bounded_harmonic_eq_zero hz (show 0≤C+1/(z-4) by positivity)
    (fun t => f t-quadrantGreenZ z t q) hpoisson hbound p
  exact sub_eq_zero.mp h

end
end SpanningTreeIsoperimetry.MassiveQuadrantUniqueness
