import SpanningTreeIsoperimetry.BoundaryHyperbolic
import SpanningTreeIsoperimetry.ScalarResolvent

/-! The general scalar path Green entry, including arbitrary interior depths.
This supplies the coordinate-exchanged boundary-loss kernel, not just row one. -/
namespace SpanningTreeIsoperimetry.BoundaryTridiagonalGreen
open BoundaryHyperbolic ScalarResolvent SmallCases
open scoped BigOperators Matrix Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

/-- The unnormalized Green numerator, with absorbing boundaries at 0 and L. -/
def fundamental (L t q x : ℝ) : ℝ :=
  if x≤q then Real.sinh (x*t)*Real.sinh ((L-q)*t)
  else Real.sinh (q*t)*Real.sinh ((L-x)*t)

theorem fundamental_left (L t q x : ℝ) (h : x≤q) :
    fundamental L t q x=Real.sinh (x*t)*Real.sinh ((L-q)*t) := by simp [fundamental,h]

theorem fundamental_right (L t q x : ℝ) (h : q≤x) :
    fundamental L t q x=Real.sinh (q*t)*Real.sinh ((L-x)*t) := by
  by_cases hx : x≤q
  · have he : x=q := le_antisymm hx h
    subst x
    simp [fundamental]
  · simp [fundamental,hx]

theorem fundamental_zero_left (L t q : ℝ) (hq : 0≤q) : fundamental L t q 0=0 := by
  rw [fundamental_left _ _ _ _ hq]
  simp

theorem fundamental_zero_right (L t q : ℝ) (hq : q≤L) : fundamental L t q L=0 := by
  rw [fundamental_right _ _ _ _ hq]
  simp

private theorem sinh_recurrence (t x : ℝ) :
    2*Real.cosh t*Real.sinh (x*t)-Real.sinh ((x+1)*t)-Real.sinh ((x-1)*t)=0 := by
  have h := sinh_neighbors t x
  rw [show t*(x+1)=(x+1)*t by ring,show t*(x-1)=(x-1)*t by ring,
    show t*x=x*t by ring] at h
  linarith

private theorem sinh_wronskian (a b t : ℝ) :
    Real.sinh (a+t)*Real.sinh b-Real.sinh a*Real.sinh (b-t)=
      Real.sinh t*Real.sinh (a+b) := by
  rw [Real.sinh_add,Real.sinh_sub,Real.sinh_add]
  ring

theorem fundamental_left_equation (L t q x : ℝ) (h : x+1≤q) :
    2*Real.cosh t*fundamental L t q x-fundamental L t q (x+1)-
      fundamental L t q (x-1)=0 := by
  rw [fundamental_left _ _ _ _ (by linarith),fundamental_left _ _ _ _ h,
    fundamental_left _ _ _ _ (by linarith)]
  have he := congrArg (fun y : ℝ => y*Real.sinh ((L-q)*t)) (sinh_recurrence t x)
  nlinarith only [he]

theorem fundamental_right_equation (L t q x : ℝ) (h : q+1≤x) :
    2*Real.cosh t*fundamental L t q x-fundamental L t q (x+1)-
      fundamental L t q (x-1)=0 := by
  rw [fundamental_right _ _ _ _ (by linarith),fundamental_right _ _ _ _ (by linarith),
    fundamental_right _ _ _ _ (by linarith)]
  have he := congrArg (fun y : ℝ => Real.sinh (q*t)*y) (sinh_recurrence t (L-x))
  rw [show L-(x+1)=L-x-1 by ring,show L-(x-1)=L-x+1 by ring]
  nlinarith only [he]

theorem fundamental_source_equation (L t q : ℝ) :
    2*Real.cosh t*fundamental L t q q-fundamental L t q (q+1)-
      fundamental L t q (q-1)=Real.sinh t*Real.sinh (L*t) := by
  rw [fundamental_left _ _ _ _ le_rfl,fundamental_right _ _ _ _ (by linarith),
    fundamental_left _ _ _ _ (by linarith)]
  have he := congrArg (fun y : ℝ => y*Real.sinh ((L-q)*t)) (sinh_recurrence t q)
  have hw := sinh_wronskian (q*t) ((L-q)*t) t
  rw [show q*t+t=(q+1)*t by ring,show (L-q)*t-t=(L-(q+1))*t by ring,
    show q*t+(L-q)*t=L*t by ring] at hw
  nlinarith only [he,hw]

theorem fundamental_lattice_equation (L t : ℝ) (i j : ℕ) :
    2*Real.cosh t*fundamental L t ((j : ℝ)+1) ((i : ℝ)+1)-
      fundamental L t ((j : ℝ)+1) ((i : ℝ)+2)-fundamental L t ((j : ℝ)+1) i=
      if i=j then Real.sinh t*Real.sinh (L*t) else 0 := by
  have ha : ((i : ℝ)+1)+1=(i : ℝ)+2 := by ring
  have hb : ((i : ℝ)+1)-1=(i : ℝ) := by ring
  rcases lt_trichotomy i j with h | h | h
  · have hg : ((i : ℝ)+1)+1≤(j : ℝ)+1 := by exact_mod_cast (show i+1+1≤j+1 by omega)
    have he := fundamental_left_equation L t ((j : ℝ)+1) ((i : ℝ)+1) hg
    simpa only [ha,hb,if_neg (ne_of_lt h)] using he
  · subst j
    simpa only [ha,hb,ite_true] using fundamental_source_equation L t ((i : ℝ)+1)
  · have hg : ((j : ℝ)+1)+1≤(i : ℝ)+1 := by exact_mod_cast (show j+1+1≤ i+1 by omega)
    have he := fundamental_right_equation L t ((j : ℝ)+1) ((i : ℝ)+1) hg
    simpa only [ha,hb,if_neg (ne_of_gt h)] using he

def tridiagonal (n : ℕ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (2*Real.cosh t) • 1-(SimpleGraph.pathGraph n).adjMatrix ℝ

def kernel (n : ℕ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  fundamental ((n : ℝ)+1) t ((j.val : ℝ)+1) ((i.val : ℝ)+1)/
    (Real.sinh t*Real.sinh (((n : ℝ)+1)*t))

theorem tridiagonal_apply (n : ℕ) (t : ℝ) (i j : Fin n) :
    tridiagonal n t i j=(if i=j then 2*Real.cosh t else 0)-
      (if i.val+1=j.val ∨ j.val+1=i.val then 1 else 0) := by
  simp [tridiagonal,SimpleGraph.adjMatrix,SimpleGraph.pathGraph_adj,Matrix.one_apply]

theorem tridiagonal_mulVec (n : ℕ) (t : ℝ) (v : Fin n → ℝ) (i : Fin n) :
    (tridiagonal n t *ᵥ v) i=2*Real.cosh t*v i-
      (if h : i.val+1<n then v ⟨i.val+1,h⟩ else 0)-
      (if h : 0 < i.val then v ⟨i.val-1,by have hi:=i.isLt; omega⟩ else 0) := by
  simp only [Matrix.mulVec,dotProduct]
  simp_rw [tridiagonal_apply,sub_mul,ite_mul,zero_mul,one_mul]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [path_neighbor_sum]
  ring

/-- The full candidate is a right inverse of the actual path Dirichlet
matrix, with both absorbing ghost values and every source site verified. -/
theorem tridiagonal_mul_kernel (n : ℕ) (t : ℝ) (ht : 0<t) :
    tridiagonal n t*kernel n t=1 := by
  ext i j
  change (tridiagonal n t *ᵥ (fun u => kernel n t u j)) i=_
  rw [tridiagonal_mulVec]
  have hp : (if h : 0 < i.val then kernel n t ⟨i.val-1,by have hi:=i.isLt; omega⟩ j else 0)=
      fundamental ((n : ℝ)+1) t ((j.val : ℝ)+1) i.val/
        (Real.sinh t*Real.sinh (((n : ℝ)+1)*t)) := by
    by_cases hi : 0 < i.val
    · rw [dif_pos hi]
      unfold kernel
      have he : ((i.val-1 : ℕ) : ℝ)+1=(i.val : ℝ) := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [he]
    · have hz : i.val=0 := by omega
      rw [dif_neg hi,hz,Nat.cast_zero,fundamental_zero_left _ _ _ (by positivity),zero_div]
  have hn : (if h : i.val+1<n then kernel n t ⟨i.val+1,h⟩ j else 0)=
      fundamental ((n : ℝ)+1) t ((j.val : ℝ)+1) ((i.val : ℝ)+2)/
        (Real.sinh t*Real.sinh (((n : ℝ)+1)*t)) := by
    by_cases hi : i.val+1<n
    · rw [dif_pos hi]
      unfold kernel
      congr 2
      push_cast
      ring
    · rw [dif_neg hi]
      have he : (i.val : ℝ)+2=(n : ℝ)+1 := by exact_mod_cast (show i.val+2=n+1 by have hi':=i.isLt; omega)
      rw [he,fundamental_zero_right _ _ _ (by exact_mod_cast (show j.val+1≤n+1 by have hj:=j.isLt; omega)),zero_div]
  rw [hp,hn]
  unfold kernel
  rw [← mul_div_assoc,← sub_div,← sub_div,fundamental_lattice_equation]
  have hden : Real.sinh t*Real.sinh (((n : ℝ)+1)*t)≠0 := by
    apply mul_ne_zero (Real.sinh_pos_iff.mpr ht).ne'
    exact (Real.sinh_pos_iff.mpr (mul_pos (by positivity) ht)).ne'
  by_cases hij : i=j
  · subst j
    simp [hden,Matrix.one_apply]
  · have hval : i.val≠j.val := by exact fun h => hij (Fin.ext h)
    simp [hval,hij,Matrix.one_apply]

/-- The formula is an actual inverse entry, not a postulated Green function. -/
theorem inverse_eq_kernel (n : ℕ) (t : ℝ) (ht : 0<t) :
    (tridiagonal n t)⁻¹=kernel n t := Matrix.inv_eq_right_inv (tridiagonal_mul_kernel n t ht)

/-- General scalar far-boundary loss identity, at arbitrary depth a. -/
theorem shifted_endpoint_loss (r a t : ℝ) (hr : 0<r) (ht : 0<t) :
    Real.exp (-(a*t))-Real.sinh ((r-a)*t)/Real.sinh (r*t)=
      2*Real.sinh (a*t)/(Real.exp (2*r*t)-1) := by
  have hs : Real.sinh (r*t)≠0 := (Real.sinh_pos_iff.mpr (mul_pos hr ht)).ne'
  calc
    _=(Real.cosh (r*t)-Real.sinh (r*t))*Real.sinh (a*t)/Real.sinh (r*t) := by
      rw [show (r-a)*t=r*t-a*t by ring,Real.sinh_sub,← Real.cosh_sub_sinh (a*t)]
      field_simp
      <;> ring
    _=(Real.exp (-(r*t))/Real.sinh (r*t))*Real.sinh (a*t) := by rw [Real.cosh_sub_sinh]; ring
    _=2*Real.sinh (a*t)/(Real.exp (2*r*t)-1) := by
      rw [exp_neg_div_sinh (r*t) (mul_pos hr ht)]
      have he : 2*(r*t)=2*r*t := by ring
      rw [he]
      ring

/-- The familiar sinh formula is the actual inverse at every ordered pair of
sites, rather than just the endpoint resolvent. -/
theorem inverse_entry_of_le (n : ℕ) (t : ℝ) (ht : 0<t) (i j : Fin n) (hij : i.val≤j.val) :
    (tridiagonal n t)⁻¹ i j=
      Real.sinh (((i.val : ℝ)+1)*t)*Real.sinh (((n : ℝ)-j.val)*t)/
        (Real.sinh t*Real.sinh (((n : ℝ)+1)*t)) := by
  rw [inverse_eq_kernel n t ht]
  unfold kernel
  rw [fundamental_left _ _ _ _ (by exact_mod_cast Nat.add_le_add_right hij 1)]
  rw [show ((n : ℝ)+1-((j.val : ℝ)+1))=(n : ℝ)-j.val by ring]

/-- The exact general one-boundary correction factor underlying the paper's
separated kernel. The first term is the corresponding half-line scalar entry. -/
theorem inverse_entry_loss_of_le (n : ℕ) (t : ℝ) (ht : 0<t) (i j : Fin n) (hij : i.val≤j.val) :
    Real.sinh (((i.val : ℝ)+1)*t)*Real.exp (-(((j.val : ℝ)+1)*t))/Real.sinh t-
      (tridiagonal n t)⁻¹ i j=
      2*Real.sinh (((i.val : ℝ)+1)*t)*Real.sinh (((j.val : ℝ)+1)*t)/
        (Real.sinh t*(Real.exp (2*((n : ℝ)+1)*t)-1)) := by
  rw [inverse_entry_of_le n t ht i j hij]
  have h := shifted_endpoint_loss ((n : ℝ)+1) ((j.val : ℝ)+1) t (by positivity) ht
  rw [show ((n : ℝ)+1-((j.val : ℝ)+1))=(n : ℝ)-j.val by ring] at h
  calc
    _=(Real.sinh (((i.val : ℝ)+1)*t)/Real.sinh t)*
        (Real.exp (-(((j.val : ℝ)+1)*t))-Real.sinh (((n : ℝ)-j.val)*t)/Real.sinh (((n : ℝ)+1)*t)) := by ring
    _=_ := by rw [h,div_mul_div_comm]; congr 1; ring

end
end SpanningTreeIsoperimetry.BoundaryTridiagonalGreen
