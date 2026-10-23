module

public import SpanningTreeIsoperimetry.PotentialKernelImageEquation
public import SpanningTreeIsoperimetry.QuadrantBoundedUniqueness

@[expose] public section

/-! The unrestricted four-image formula for the actual quadrant Green
kernel. Its uniform bound follows directly from the bounded sine numerator;
the finite-box barrier proves uniqueness of the already checked Poisson
solution. No diagonal-value formula or continuum Green kernel is assumed. -/
namespace SpanningTreeIsoperimetry.PotentialKernelImages
open PotentialKernelIntegral PotentialKernelHarmonic PotentialKernelImageEquation
open Ferrers BoundaryGreenBounds QuadrantBoundedUniqueness MeasureTheory
open scoped ENNReal Topology Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def sineFactor (a b : ℕ) (θ : ℝ) : ℝ :=
  Real.sin (((a : ℝ)+1)*θ)*Real.sin (((b : ℝ)+1)*θ)

def imageDensity (p q : Point) (θ φ : ℝ) : ℝ :=
  (-density (Nat.dist p.1 q.1) (Nat.dist p.2 q.2) θ φ+
    density (p.1+q.1+2) (Nat.dist p.2 q.2) θ φ+
    density (Nat.dist p.1 q.1) (p.2+q.2+2) θ φ-
    density (p.1+q.1+2) (p.2+q.2+2) θ φ)/4

theorem cos_distance (a b : ℕ) (θ : ℝ) :
    Real.cos ((Nat.dist a b : ℝ)*θ)=Real.cos (((a : ℝ)-b)*θ) := by
  by_cases hab : a≤b
  · rw [Nat.dist_eq_sub_of_le hab,Nat.cast_sub hab]
    rw [show ((b : ℝ)-a)*θ= -(((a : ℝ)-b)*θ) by ring,Real.cos_neg]
  · rw [Nat.dist_eq_sub_of_le_right (by omega : b≤a),Nat.cast_sub (by omega : b≤a)]

theorem cosine_image_difference (a b : ℕ) (θ : ℝ) :
    Real.cos ((Nat.dist a b : ℝ)*θ)-Real.cos (((a+b+2 : ℕ) : ℝ)*θ)=2*sineFactor a b θ := by
  rw [cos_distance]
  have hm : ((a : ℝ)-b)*θ=((a : ℝ)+1)*θ-((b : ℝ)+1)*θ := by ring
  have hp : (((a+b+2 : ℕ) : ℝ)*θ)=((a : ℝ)+1)*θ+((b : ℝ)+1)*θ := by push_cast; ring
  rw [hm,hp,Real.cos_sub,Real.cos_add,sineFactor]
  ring

theorem imageDensity_eq_sine (p q : Point) (θ φ : ℝ) :
    imageDensity p q θ φ=sineFactor p.1 q.1 θ*sineFactor p.2 q.2 φ/denominator θ φ := by
  have hx := cosine_image_difference p.1 q.1 θ
  have hy := cosine_image_difference p.2 q.2 φ
  have h := congrArg₂ (fun x y : ℝ => x*y) hx hy
  unfold imageDensity density
  by_cases hd : denominator θ φ=0
  · simp only [hd,div_zero,zero_div,neg_zero,zero_add,sub_zero]
  · field_simp [hd]
    simp only [mul_comm] at h ⊢
    nlinarith only [h]

theorem sineFactor_bound (a b : ℕ) (θ : ℝ) :
    |sineFactor a b θ|≤((b : ℝ)+1)*|Real.sin θ| := by
  rw [sineFactor,abs_mul]
  calc
    _≤1*|Real.sin (((b : ℝ)+1)*θ)| :=
      mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
    _≤((b : ℝ)+1)*|Real.sin θ| := by
      simpa only [one_mul,Nat.cast_add,Nat.cast_one] using
        BoundaryKernelBounds.abs_sin_nat_mul_le (b+1) θ

theorem abs_sine_pair_le (θ φ : ℝ) : |Real.sin θ*Real.sin φ|≤2*denominator θ φ := by
  have hs := sq_nonneg (|Real.sin θ| - |Real.sin φ|)
  simp only [sub_sq,sq_abs] at hs
  have hx := Real.sin_sq_add_cos_sq θ
  have hy := Real.sin_sq_add_cos_sq φ
  have hx' := sq_nonneg (1-Real.cos θ)
  have hy' := sq_nonneg (1-Real.cos φ)
  rw [abs_mul]
  unfold denominator
  nlinarith only [hs,hx,hy,hx',hy']

/-- A bound independent of the evaluation site p; q is fixed. -/
theorem imageDensity_bound (p q : Point) (θ φ : ℝ) :
    |imageDensity p q θ φ|≤2*((q.1 : ℝ)+1)*((q.2 : ℝ)+1) := by
  rw [imageDensity_eq_sine,abs_div,abs_of_nonneg (denominator_nonneg θ φ)]
  by_cases hd : denominator θ φ=0
  · rw [hd,div_zero]
    positivity
  have hd0 : 0<denominator θ φ := lt_of_le_of_ne (denominator_nonneg θ φ) (Ne.symm hd)
  apply (div_le_iff₀ hd0).mpr
  have hn : |sineFactor p.1 q.1 θ*sineFactor p.2 q.2 φ|≤
      ((q.1 : ℝ)+1)*((q.2 : ℝ)+1)*(2*denominator θ φ) := by
    calc
      _=|sineFactor p.1 q.1 θ| * |sineFactor p.2 q.2 φ| := abs_mul _ _
      _≤(((q.1 : ℝ)+1)*|Real.sin θ|)*(((q.2 : ℝ)+1)*|Real.sin φ|) :=
        mul_le_mul (sineFactor_bound _ _ _) (sineFactor_bound _ _ _) (abs_nonneg _) (by positivity)
      _=((q.1 : ℝ)+1)*((q.2 : ℝ)+1)*|Real.sin θ*Real.sin φ| := by rw [abs_mul]; ring
      _≤_ := mul_le_mul_of_nonneg_left (abs_sine_pair_le θ φ) (by positivity)
  nlinarith only [hn]

theorem imageDensity_integrable (p q : Point) :
    IntegrableOn (fun t : ℝ × ℝ => imageDensity p q t.1 t.2) frequencySquare := by
  have h1 := density_integrable (Nat.dist p.1 q.1) (Nat.dist p.2 q.2)
  have h2 := density_integrable (p.1+q.1+2) (Nat.dist p.2 q.2)
  have h3 := density_integrable (Nat.dist p.1 q.1) (p.2+q.2+2)
  have h4 := density_integrable (p.1+q.1+2) (p.2+q.2+2)
  exact (((h1.neg.add h2).add h3).sub h4).div_const 4

theorem image_eq_integral (p q : Point) : image p q=
    (1/Real.pi^2)*∫ t in frequencySquare,imageDensity p q t.1 t.2 := by
  have h1 := density_integrable (Nat.dist p.1 q.1) (Nat.dist p.2 q.2)
  have h2 := density_integrable (p.1+q.1+2) (Nat.dist p.2 q.2)
  have h3 := density_integrable (Nat.dist p.1 q.1) (p.2+q.2+2)
  have h4 := density_integrable (p.1+q.1+2) (p.2+q.2+2)
  have h12 : Integrable (fun t : ℝ × ℝ =>
      -density (Nat.dist p.1 q.1) (Nat.dist p.2 q.2) t.1 t.2+
        density (p.1+q.1+2) (Nat.dist p.2 q.2) t.1 t.2)
      (volume.restrict frequencySquare) := h1.neg.add h2
  have h123 : Integrable (fun t : ℝ × ℝ =>
      -density (Nat.dist p.1 q.1) (Nat.dist p.2 q.2) t.1 t.2+
        density (p.1+q.1+2) (Nat.dist p.2 q.2) t.1 t.2+
        density (Nat.dist p.1 q.1) (p.2+q.2+2) t.1 t.2)
      (volume.restrict frequencySquare) := h12.add h3
  have h1n : Integrable (fun t : ℝ × ℝ =>
      -density (Nat.dist p.1 q.1) (Nat.dist p.2 q.2) t.1 t.2)
      (volume.restrict frequencySquare) := h1.neg
  rw [image_formula]
  unfold imageDensity potential
  rw [integral_div,integral_sub h123 h4,integral_add h12 h3,integral_add h1n h2,integral_neg]
  ring

theorem square_integral_one : (∫ t : ℝ × ℝ in frequencySquare,(1 : ℝ))=Real.pi^2 := by
  have h := cosine_product_integral 0 0
  norm_num at h
  simpa [pow_two] using h

theorem square_integral_const (C : ℝ) : (∫ t : ℝ × ℝ in frequencySquare,C)=C*Real.pi^2 := by
  have h := integral_const_mul (μ := volume.restrict frequencySquare) C (fun _ : ℝ × ℝ => (1 : ℝ))
  simpa only [mul_one,square_integral_one] using h

theorem image_bound (p q : Point) : |image p q|≤2*((q.1 : ℝ)+1)*((q.2 : ℝ)+1) := by
  let C := 2*((q.1 : ℝ)+1)*((q.2 : ℝ)+1)
  have hInt := imageDensity_integrable p q
  have hAbsInt : Integrable (fun t : ℝ × ℝ => |imageDensity p q t.1 t.2|)
      (volume.restrict frequencySquare) := by simpa only [Real.norm_eq_abs] using hInt.norm
  have hcInt : Integrable (fun _ : ℝ × ℝ => C) (volume.restrict frequencySquare) :=
    integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hnorm : |∫ t in frequencySquare,imageDensity p q t.1 t.2|≤
      ∫ t in frequencySquare,|imageDensity p q t.1 t.2| := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (μ := volume.restrict frequencySquare) (fun t : ℝ × ℝ => imageDensity p q t.1 t.2)
  have hmono := integral_mono hAbsInt hcInt (fun t => imageDensity_bound p q t.1 t.2)
  rw [square_integral_const] at hmono
  rw [image_eq_integral,abs_mul,abs_of_nonneg (by positivity : (0 : ℝ)≤1/Real.pi^2)]
  calc
    _≤(1/Real.pi^2)*(C*Real.pi^2) := mul_le_mul_of_nonneg_left (hnorm.trans hmono) (by positivity)
    _=C := by field_simp [Real.pi_ne_zero]

/-- Unrestricted image formula for the actual quadrant Green function. -/
theorem quadrantGreen_eq_image (p q : Point) : quadrantGreen p q=image p q := by
  apply (eq_quadrantGreen_of_bounded_poisson (C := 2*((q.1 : ℝ)+1)*((q.2 : ℝ)+1))
    (by positivity) q (fun p => image p q) (fun p => image_bound p q)
    (fun p => image_poisson p q) p).symm

theorem quadrantGreen_image_formula (p q : Point) : quadrantGreen p q=
    (-potential (Nat.dist p.1 q.1) (Nat.dist p.2 q.2)+
      potential (p.1+q.1+2) (Nat.dist p.2 q.2)+
      potential (Nat.dist p.1 q.1) (p.2+q.2+2)-
      potential (p.1+q.1+2) (p.2+q.2+2))/4 := by
  rw [quadrantGreen_eq_image,image_formula]

/-- Positive-face-coordinate spelling of the same actual kernel, matching
Appendix B's killing axes and image displacements. -/
theorem quadrantGreen_image_positive {x y u v : ℕ}
    (hx : 1≤x) (hy : 1≤y) (hu : 1≤u) (hv : 1≤v) :
    quadrantGreen (x-1,y-1) (u-1,v-1)=
      (-potential (Nat.dist x u) (Nat.dist y v)+potential (x+u) (Nat.dist y v)+
        potential (Nat.dist x u) (y+v)-potential (x+u) (y+v))/4 := by
  have hdx : Nat.dist (x-1) (u-1)=Nat.dist x u := by simp only [Nat.dist]; omega
  have hdy : Nat.dist (y-1) (v-1)=Nat.dist y v := by simp only [Nat.dist]; omega
  have hxs : x-1+(u-1)+2=x+u := by omega
  have hys : y-1+(v-1)+2=y+v := by omega
  simpa only [quadrantGreen_image_formula,Prod.fst,Prod.snd,hdx,hdy,hxs,hys]

end
end SpanningTreeIsoperimetry.PotentialKernelImages
