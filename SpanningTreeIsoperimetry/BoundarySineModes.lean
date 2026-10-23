module

public import SpanningTreeIsoperimetry.ScalarResolvent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

@[expose] public section

set_option backward.privateInPublic true

/-! Explicit finite Dirichlet sine modes for the one-coordinate Green
separation. These concern the actual path operator used in the continuants. -/
namespace SpanningTreeIsoperimetry.BoundarySineModes
open ScalarResolvent
open scoped BigOperators Matrix Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def angle (n : ℕ) (j : Fin n) : ℝ := Real.pi*((j.val : ℝ)+1)/((n : ℝ)+1)

def mode (n : ℕ) (j i : Fin n) : ℝ := Real.sin (angle n j*((i.val : ℝ)+1))

def eigenvalue (n : ℕ) (j : Fin n) : ℝ := 4-2*Real.cos (angle n j)

theorem angle_pos (n : ℕ) (j : Fin n) : 0<angle n j := by unfold angle; positivity

theorem angle_lt_pi (n : ℕ) (j : Fin n) : angle n j<Real.pi := by
  unfold angle
  rw [div_lt_iff₀ (by positivity : (0 : ℝ)<n+1)]
  have hj : (j.val : ℝ)<n := by exact_mod_cast j.isLt
  nlinarith [Real.pi_pos]

theorem angle_times_width (n : ℕ) (j : Fin n) : angle n j*((n : ℝ)+1)=Real.pi*(j.val+1) := by
  unfold angle
  exact div_mul_cancel₀ _ (by positivity)

theorem ghost_right (n : ℕ) (j : Fin n) : Real.sin (angle n j*((n : ℝ)+1))=0 := by
  rw [angle_times_width]
  have he : Real.pi*((j.val : ℝ)+1)=((j.val+1 : ℕ) : ℝ)*Real.pi := by push_cast; ring
  rw [he]
  exact Real.sin_nat_mul_pi _

theorem sine_neighbors (t x : ℝ) :
    Real.sin (t*(x+1))+Real.sin (t*(x-1))=2*Real.cos t*Real.sin (t*x) := by
  rw [mul_add,mul_sub,mul_one,Real.sin_add,Real.sin_sub]
  ring

/-- Every sine mode is an actual eigenvector of the finite Dirichlet path
operator, with the zero ghost values accounted for at both endpoints. -/
theorem mode_mulVec (n : ℕ) (j : Fin n) :
    pathOperator n *ᵥ mode n j=eigenvalue n j • mode n j := by
  ext i
  simp only [Matrix.mulVec,dotProduct]
  simp_rw [pathOperator_apply,sub_mul,ite_mul,zero_mul,one_mul]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [path_neighbor_sum]
  have hp : (if h : (0 : ℕ) < i.val then mode n j ⟨i.val-1,by have hi:=i.isLt; omega⟩ else 0)=
      Real.sin (angle n j*(i.val : ℝ)) := by
    by_cases hi : (0 : ℕ) < i.val
    · rw [dif_pos hi]
      unfold mode
      have he : ((i.val-1 : ℕ) : ℝ)+1=(i.val : ℝ) := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [he]
    · have hz : i.val=0 := by omega
      simp [hi,hz]
  have hn : (if h : i.val + 1 < n then mode n j ⟨i.val+1,h⟩ else 0)=
      Real.sin (angle n j*((i.val : ℝ)+2)) := by
    by_cases hi : i.val + 1 < n
    · rw [dif_pos hi]
      unfold mode
      congr 2
      push_cast
      ring
    · rw [dif_neg hi]
      have he : (i.val : ℝ)+2=(n : ℝ)+1 := by
        have ht : i.val+1=n := by have hi':=i.isLt; omega
        exact_mod_cast (show i.val+2=n+1 by omega)
      rw [he,ghost_right]
  rw [hp,hn]
  have h := sine_neighbors (angle n j) ((i.val : ℝ)+1)
  have hm : ((i.val : ℝ)+1)-1=(i.val : ℝ) := by ring
  have ha : ((i.val : ℝ)+1)+1=(i.val : ℝ)+2 := by ring
  rw [hm,ha] at h
  simp only [eigenvalue,mode,Pi.smul_apply,smul_eq_mul]
  nlinarith only [h]

theorem angle_injective (n : ℕ) : Function.Injective (angle n) := by
  intro j k h
  have he := congrArg (fun x : ℝ => x*((n : ℝ)+1)) h
  rw [angle_times_width,angle_times_width] at he
  apply Fin.ext
  have hval : (j.val : ℝ)=(k.val : ℝ) := by nlinarith [Real.pi_pos]
  exact_mod_cast hval

theorem eigenvalue_injective (n : ℕ) : Function.Injective (eigenvalue n) := by
  intro j k h
  have hc : Real.cos (angle n j)=Real.cos (angle n k) := by unfold eigenvalue at h; linarith
  apply angle_injective n
  exact Real.strictAntiOn_cos.injOn ⟨(angle_pos n j).le,(angle_lt_pi n j).le⟩
    ⟨(angle_pos n k).le,(angle_lt_pi n k).le⟩ hc

theorem mode_orthogonal (n : ℕ) (j k : Fin n) (hjk : j≠k) :
    mode n j ⬝ᵥ mode n k=0 := by
  have h := (pathOperator_isSymm n).dotProduct_mulVec_comm (x := mode n j) (y := mode n k)
  rw [mode_mulVec,mode_mulVec,dotProduct_smul,dotProduct_smul,
    dotProduct_comm (mode n k) (mode n j)] at h
  simp only [smul_eq_mul] at h
  have he : eigenvalue n k-eigenvalue n j≠0 := by
    intro he
    have hh := eigenvalue_injective n (sub_eq_zero.mp he)
    exact hjk hh.symm
  have hz : (eigenvalue n k-eigenvalue n j)*(mode n j ⬝ᵥ mode n k)=0 := by nlinarith only [h]
  exact (mul_eq_zero.mp hz).resolve_left he

private theorem cosine_sum_zero (n : ℕ) (j : Fin n) :
    (∑ x ∈ Finset.range (n+1), Real.cos (2*angle n j*x))=0 := by
  have h := Real.sin_mul_sum_cos (n+1) (2*angle n j) 0
  have hθ : (2*angle n j)/2=angle n j := by ring
  have hθn : ((n+1 : ℕ) : ℝ)*(2*angle n j)/2=angle n j*((n : ℝ)+1) := by push_cast; ring
  simp only [hθ,hθn,ghost_right,zero_mul,add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left
    (Real.sin_pos_of_pos_of_lt_pi (angle_pos n j) (angle_lt_pi n j)).ne'

/-- Exact normalization of every finite Dirichlet sine mode. -/
theorem mode_norm_sq (n : ℕ) (j : Fin n) :
    mode n j ⬝ᵥ mode n j=((n : ℝ)+1)/2 := by
  have hp (x : ℕ) : 2*Real.sin (angle n j*x)^2=1-Real.cos (2*angle n j*x) := by
    have hc := Real.cos_two_mul (angle n j*x)
    have hs := Real.sin_sq_add_cos_sq (angle n j*x)
    have he : 2*angle n j*x=2*(angle n j*x) := by ring
    rw [he]
    nlinarith only [hc,hs]
  have hsum := Finset.sum_congr (rfl : Finset.range (n+1)=Finset.range (n+1)) (fun x _ => hp x)
  simp only [← Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,
    nsmul_eq_mul,mul_one,cosine_sum_zero,sub_zero] at hsum
  rw [Finset.sum_range_succ'] at hsum
  simp only [Nat.cast_zero,mul_zero,Real.sin_zero,zero_pow (by decide : 2≠0),add_zero] at hsum
  have hv : (∑ x : Fin n, Real.sin (angle n j*((x.val : ℝ)+1))^2)=
      ∑ x ∈ Finset.range n, Real.sin (angle n j*((x : ℝ)+1))^2 :=
    Fin.sum_univ_eq_sum_range (fun x => Real.sin (angle n j*((x : ℝ)+1))^2) n
  simp only [dotProduct,mode,← pow_two]
  rw [hv]
  push_cast at hsum
  linarith

/-- Columns form a complete normalized orthogonal system. -/
def sineMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j => mode n j i

theorem sineMatrix_gram (n : ℕ) :
    (sineMatrix n).transpose*sineMatrix n=(((n : ℝ)+1)/2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext j k
  change (mode n j ⬝ᵥ mode n k)=_
  by_cases h : j=k
  · subst k
    simp only [mode_norm_sq,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,ite_true,mul_one]
  · simp only [mode_orthogonal n j k h,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,h,ite_false,mul_zero]

end
end SpanningTreeIsoperimetry.BoundarySineModes

