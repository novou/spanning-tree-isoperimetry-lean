import SpanningTreeIsoperimetry.MassiveQuadrantUniqueness
import SpanningTreeIsoperimetry.RegularizedStripSymbol
import SpanningTreeIsoperimetry.PotentialKernelImages
import SpanningTreeIsoperimetry.BoundarySineModes

/-! Boundary-source sine separation for the actual z>4 quadrant resolvent,
followed by its Toeplitz-minus-Hankel symbol identity. Determinant and
loop-energy normalization are deliberately separate statements. -/
namespace SpanningTreeIsoperimetry.RegularizedBoundaryKernel
open Ferrers BoundaryGreenLoss RegularizedQuadrantGreen MassiveQuadrantUniqueness
open RegularizedStripSymbol PotentialKernelImages PotentialKernelHarmonic MeasureTheory
open scoped BigOperators Matrix Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def vertical (z : ℝ) (y : ℕ) (θ : ℝ) : ℝ := (symbol z θ)^(y+1)

theorem vertical_eq_exp (z : ℝ) (y : ℕ) (θ : ℝ) :
    vertical z y θ=Real.exp (-((y : ℝ)+1)*gammaZ z θ) := by
  rw [vertical,symbol,← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem symbol_characteristic {z : ℝ} (hz : 4<z) (θ : ℝ) :
    (z-2*Real.cos θ)*symbol z θ=1+(symbol z θ)^2 := by
  have hc := Real.cosh_arcosh (show 1≤z/2-Real.cos θ by linarith [Real.cos_le_one θ])
  change Real.cosh (gammaZ z θ)=z/2-Real.cos θ at hc
  rw [Real.cosh_eq] at hc
  change (Real.exp (gammaZ z θ)+symbol z θ)/2=z/2-Real.cos θ at hc
  have he : Real.exp (gammaZ z θ)*symbol z θ=1 := by
    rw [symbol,← Real.exp_add,add_neg_cancel,Real.exp_zero]
  have hm := congrArg (fun t : ℝ => t*symbol z θ) hc
  nlinarith only [hm,he]

theorem vertical_recurrence {z : ℝ} (hz : 4<z) (y : ℕ) (θ : ℝ) :
    (z-2*Real.cos θ)*vertical z y θ-vertical z (y+1) θ-
      (if y=0 then 0 else vertical z (y-1) θ)=if y=0 then 1 else 0 := by
  have hc := symbol_characteristic hz θ
  by_cases hy : y=0
  · subst y
    simp only [vertical,zero_add,pow_one,ite_true,sub_zero]
    change (z-2*Real.cos θ)*symbol z θ-(symbol z θ)^2=1
    nlinarith only [hc]
  · have hp : y-1+1=y := by omega
    simp only [hy,ite_false,vertical,hp]
    have h := congrArg (fun t : ℝ => t*(symbol z θ)^y) hc
    simp only [pow_succ,pow_two] at h ⊢
    nlinarith only [h]

theorem continuous_symbol {z : ℝ} (hz : 4<z) : Continuous (symbol z) := by
  exact Real.continuous_exp.comp (contDiff_gammaZ hz).continuous.neg

theorem vertical_bounds {z : ℝ} (hz : 4<z) (y : ℕ) (θ : ℝ) :
    0≤vertical z y θ ∧ vertical z y θ≤1 := by
  obtain ⟨hs,hs1⟩ := symbol_bounds hz θ
  exact ⟨pow_nonneg hs.le _,pow_le_one₀ hs.le hs1.le⟩

def term (z : ℝ) (j : ℕ) (p : Point) (θ : ℝ) : ℝ := sineFactor p.1 j θ*vertical z p.2 θ

def kernel (z : ℝ) (j : ℕ) (p : Point) : ℝ :=
  (2/Real.pi)*∫ θ in (0 : ℝ)..Real.pi,term z j p θ

theorem term_continuous {z : ℝ} (hz : 4<z) (j : ℕ) (p : Point) : Continuous (term z j p) := by
  have hs := continuous_symbol hz
  unfold term sineFactor vertical
  fun_prop

theorem term_integrable {z : ℝ} (hz : 4<z) (j : ℕ) (p : Point) :
    IntervalIntegrable (term z j p) volume 0 Real.pi := (term_continuous hz j p).intervalIntegrable _ _

theorem term_abs_le {z : ℝ} (hz : 4<z) (j : ℕ) (p : Point) (θ : ℝ) : |term z j p θ|≤1 := by
  obtain ⟨hv0,hv1⟩ := vertical_bounds hz p.2 θ
  rw [term,sineFactor,abs_mul,abs_mul,abs_of_nonneg hv0]
  have hs : |Real.sin (((p.1 : ℝ)+1)*θ)| * |Real.sin (((j : ℝ)+1)*θ)|≤1 := by
    simpa only [one_mul] using mul_le_mul (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
      (abs_nonneg _) (by norm_num : (0 : ℝ)≤1)
  exact (mul_le_mul_of_nonneg_right hs hv0).trans (by simpa only [one_mul] using hv1)

theorem kernel_bound {z : ℝ} (hz : 4<z) (j : ℕ) (p : Point) : |kernel z j p|≤2 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := term z j p)
    (a := (0 : ℝ)) (b := Real.pi) (C := (1 : ℝ))
    (fun θ _ => by simpa only [Real.norm_eq_abs] using term_abs_le hz j p θ)
  have hi : |∫ θ in (0 : ℝ)..Real.pi,term z j p θ|≤Real.pi := by
    simpa only [Real.norm_eq_abs,sub_zero,abs_of_pos Real.pi_pos,one_mul] using h
  rw [kernel,abs_mul,abs_of_nonneg (by positivity : (0 : ℝ)≤2/Real.pi)]
  calc
    _≤(2/Real.pi)*Real.pi := mul_le_mul_of_nonneg_left hi (by positivity)
    _=2 := by field_simp

theorem sine_neighbors (i : ℕ) (θ : ℝ) :
    Real.sin (((i : ℝ)+2)*θ)+Real.sin ((i : ℝ)*θ)=
      2*Real.cos θ*Real.sin (((i : ℝ)+1)*θ) := by
  have h := BoundarySineModes.sine_neighbors θ ((i : ℝ)+1)
  have h1 : θ*((i : ℝ)+1+1)=((i : ℝ)+2)*θ := by ring
  have h2 : θ*((i : ℝ)+1-1)=(i : ℝ)*θ := by ring
  have h3 : θ*((i : ℝ)+1)=((i : ℝ)+1)*θ := by ring
  simpa only [h1,h2,h3] using h

theorem term_west (z : ℝ) (j : ℕ) (p : Point) (θ : ℝ) :
    (if p.1=0 then 0 else term z j (p.1-1,p.2) θ)=
      Real.sin ((p.1 : ℝ)*θ)*Real.sin (((j : ℝ)+1)*θ)*vertical z p.2 θ := by
  by_cases hx : p.1=0
  · simp [hx]
  · have he : ((p.1-1 : ℕ) : ℝ)+1=(p.1 : ℝ) := by
      rw [Nat.cast_sub (by omega : 1≤p.1)]
      norm_num
    simp only [hx,ite_false,term,sineFactor,Prod.fst,Prod.snd,he]

theorem term_south (z : ℝ) (j : ℕ) (p : Point) (θ : ℝ) :
    (if p.2=0 then 0 else term z j (p.1,p.2-1) θ)=
      sineFactor p.1 j θ*(if p.2=0 then 0 else vertical z (p.2-1) θ) := by
  by_cases hy : p.2=0 <;> simp only [hy,ite_true,ite_false,term,Prod.fst,Prod.snd,mul_zero]

theorem term_poisson {z : ℝ} (hz : 4<z) (j : ℕ) (p : Point) (θ : ℝ) :
    laplacianZ z (fun t => term z j t θ) p=if p.2=0 then sineFactor p.1 j θ else 0 := by
  have hx := congrArg (fun t : ℝ => t*Real.sin (((j : ℝ)+1)*θ)*vertical z p.2 θ)
    (sine_neighbors p.1 θ)
  have hy := congrArg (fun t : ℝ => sineFactor p.1 j θ*t) (vertical_recurrence hz p.2 θ)
  rw [laplacianZ_explicit,term_west,term_south]
  simp only [term,sineFactor,Prod.fst,Prod.snd,Nat.cast_add,Nat.cast_one] at hx hy ⊢
  have he : (p.1 : ℝ)+1+1=(p.1 : ℝ)+2 := by ring
  rw [he]
  by_cases hp : p.2=0 <;> simp only [hp,ite_true,ite_false,mul_zero,mul_one] at hx hy ⊢ <;>
    nlinarith only [hx,hy]

theorem laplacianZ_const_mul (z c : ℝ) (f : Point → ℝ) (p : Point) :
    laplacianZ z (fun t => c*f t) p=c*laplacianZ z f p := by
  simp only [laplacianZ_explicit]
  split_ifs <;> ring

/-- Scalar integration commutes with the finite killed-lattice row. -/
theorem integral_laplacianZ (z : ℝ) (F : Point → ℝ → ℝ)
    (hF : ∀ p,IntervalIntegrable (F p) volume 0 Real.pi) (p : Point) :
    (∫ θ in (0 : ℝ)..Real.pi,laplacianZ z (fun t => F t θ) p)=
      laplacianZ z (fun t => ∫ θ in (0 : ℝ)..Real.pi,F t θ) p := by
  let L : ℝ → ℝ := if p.1=0 then fun _ => 0 else F (p.1-1,p.2)
  let D : ℝ → ℝ := if p.2=0 then fun _ => 0 else F (p.1,p.2-1)
  have hL : IntervalIntegrable L volume 0 Real.pi := by
    dsimp only [L]
    split_ifs
    · exact intervalIntegrable_const
    · exact hF _
  have hD : IntervalIntegrable D volume 0 Real.pi := by
    dsimp only [D]
    split_ifs
    · exact intervalIntegrable_const
    · exact hF _
  have hLv (θ : ℝ) : L θ=if p.1=0 then 0 else F (p.1-1,p.2) θ := by
    dsimp [L]
    split_ifs <;> rfl
  have hDv (θ : ℝ) : D θ=if p.2=0 then 0 else F (p.1,p.2-1) θ := by
    dsimp [D]
    split_ifs <;> rfl
  have hLi : (∫ θ in (0 : ℝ)..Real.pi,L θ)=if p.1=0 then 0 else ∫ θ in (0 : ℝ)..Real.pi,F (p.1-1,p.2) θ := by
    dsimp [L]
    split_ifs <;> simp
  have hDi : (∫ θ in (0 : ℝ)..Real.pi,D θ)=if p.2=0 then 0 else ∫ θ in (0 : ℝ)..Real.pi,F (p.1,p.2-1) θ := by
    dsimp [D]
    split_ifs <;> simp
  have h1 : IntervalIntegrable (fun θ => z*F p θ-F (p.1+1,p.2) θ) volume 0 Real.pi :=
    ((hF p).const_mul z).sub (hF _)
  have h2 : IntervalIntegrable (fun θ => z*F p θ-F (p.1+1,p.2) θ-L θ) volume 0 Real.pi := h1.sub hL
  have h3 : IntervalIntegrable (fun θ => z*F p θ-F (p.1+1,p.2) θ-L θ-F (p.1,p.2+1) θ) volume 0 Real.pi := h2.sub (hF _)
  have he : (fun θ => laplacianZ z (fun t => F t θ) p)=
      fun θ => z*F p θ-F (p.1+1,p.2) θ-L θ-F (p.1,p.2+1) θ-D θ := by
    funext θ
    simp only [laplacianZ_explicit,hLv,hDv]
  rw [he,intervalIntegral.integral_sub h3 hD,intervalIntegral.integral_sub h2 (hF _),
    intervalIntegral.integral_sub h1 hL,intervalIntegral.integral_sub ((hF p).const_mul z) (hF _),
    intervalIntegral.integral_const_mul,hLi,hDi,laplacianZ_explicit]

theorem cosine_interval (n : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi,Real.cos ((n : ℝ)*θ))=if n=0 then Real.pi else 0 := by
  rw [intervalIntegral.integral_of_le Real.pi_pos.le,← integral_Icc_eq_integral_Ioc]
  exact cosine_integral n

theorem sine_orthogonality (i j : ℕ) :
    (2/Real.pi)*(∫ θ in (0 : ℝ)..Real.pi,sineFactor i j θ)=if i=j then 1 else 0 := by
  have hc (n : ℕ) : IntervalIntegrable (fun θ : ℝ => Real.cos ((n : ℝ)*θ)) volume 0 Real.pi :=
    (show Continuous (fun θ : ℝ => Real.cos ((n : ℝ)*θ)) by fun_prop).intervalIntegrable _ _
  have h := intervalIntegral.integral_congr (μ := volume) (a := (0 : ℝ)) (b := Real.pi)
    (f := fun θ => Real.cos ((Nat.dist i j : ℝ)*θ)-Real.cos (((i+j+2 : ℕ) : ℝ)*θ))
    (g := fun θ => 2*sineFactor i j θ) (fun θ _ => cosine_image_difference i j θ)
  rw [intervalIntegral.integral_sub (hc _) (hc _),cosine_interval,cosine_interval,
    intervalIntegral.integral_const_mul] at h
  have hsum : i+j+2≠0 := by omega
  simp only [hsum,ite_false,sub_zero] at h
  by_cases hij : i=j
  · subst j
    simp only [Nat.dist_self,ite_true] at h
    simp only [ite_true]
    field_simp [Real.pi_ne_zero]
    linarith only [h]
  · have hd : Nat.dist i j≠0 := fun h => hij (Nat.eq_of_dist_eq_zero h)
    simp only [hd,hij,ite_false] at h ⊢
    have hzero : (∫ θ in (0 : ℝ)..Real.pi,sineFactor i j θ)=0 := by linarith only [h]
    rw [hzero,mul_zero]

theorem kernel_poisson {z : ℝ} (hz : 4<z) (j : ℕ) (p : Point) :
    laplacianZ z (kernel z j) p=if p=(j,0) then 1 else 0 := by
  change laplacianZ z (fun t => (2/Real.pi)*∫ θ in (0 : ℝ)..Real.pi,term z j t θ) p=_
  rw [laplacianZ_const_mul,← integral_laplacianZ z (term z j) (term_integrable hz j)]
  simp_rw [term_poisson hz]
  by_cases hy : p.2=0 <;> simp [hy,Prod.ext_iff,sine_orthogonality]

/-- The sine-exponential candidate is the actual exhausted boundary-source
resolvent, with both the source equation and boundedness discharged. -/
theorem kernel_eq_quadrantGreenZ {z : ℝ} (hz : 4<z) (j : ℕ) (p : Point) :
    kernel z j p=quadrantGreenZ z p (j,0) :=
  eq_quadrantGreenZ_of_bounded_poisson hz (by norm_num : (0 : ℝ)≤2) (j,0)
    (kernel z j) (kernel_bound hz j) (kernel_poisson hz j) p

theorem boundary_entry_integral {z : ℝ} (hz : 4<z) (i j : ℕ) :
    quadrantGreenZ z (i,0) (j,0)=
      (2/Real.pi)*∫ θ in (0 : ℝ)..Real.pi,sineFactor i j θ*Real.exp (-gammaZ z θ) := by
  rw [← kernel_eq_quadrantGreenZ hz j (i,0)]
  simp only [kernel,term,vertical,Prod.fst,Prod.snd,zero_add,pow_one,symbol]

/-- Cosine coefficients of the actual positive regularized Green symbol.
These are distinct from the logarithmic coefficients coefficientZ. -/
def symbolCoefficient (z : ℝ) (n : ℕ) : ℝ :=
  (1/Real.pi)*∫ θ in (0 : ℝ)..Real.pi,symbol z θ*Real.cos ((n : ℝ)*θ)

theorem boundary_toeplitz_hankel {z : ℝ} (hz : 4<z) (i j : ℕ) :
    quadrantGreenZ z (i,0) (j,0)=symbolCoefficient z (Nat.dist i j)-symbolCoefficient z (i+j+2) := by
  have hc (n : ℕ) : IntervalIntegrable (fun θ => symbol z θ*Real.cos ((n : ℝ)*θ)) volume 0 Real.pi :=
    ((continuous_symbol hz).mul (by fun_prop)).intervalIntegrable _ _
  have h := intervalIntegral.integral_congr (μ := volume) (a := (0 : ℝ)) (b := Real.pi)
    (f := fun θ => 2*(sineFactor i j θ*symbol z θ))
    (g := fun θ => symbol z θ*Real.cos ((Nat.dist i j : ℝ)*θ)-
      symbol z θ*Real.cos (((i+j+2 : ℕ) : ℝ)*θ)) (by
      intro θ _
      have hh := congrArg (fun t : ℝ => t*symbol z θ) (cosine_image_difference i j θ)
      nlinarith only [hh])
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub (hc _) (hc _)] at h
  rw [← kernel_eq_quadrantGreenZ hz j (i,0)]
  simp only [kernel,term,vertical,Prod.fst,Prod.snd,zero_add,pow_one]
  unfold symbolCoefficient
  linear_combination (1/Real.pi)*h

def boundaryMatrix (z : ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => quadrantGreenZ z (i.val,0) (j.val,0)

def toeplitzHankelMatrix (z : ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => symbolCoefficient z (Nat.dist i.val j.val)-symbolCoefficient z (i.val+j.val+2)

theorem boundaryMatrix_eq_toeplitzHankel {z : ℝ} (hz : 4<z) (k : ℕ) :
    boundaryMatrix z k=toeplitzHankelMatrix z k := by
  ext i j
  exact boundary_toeplitz_hankel hz i.val j.val

end
end SpanningTreeIsoperimetry.RegularizedBoundaryKernel
