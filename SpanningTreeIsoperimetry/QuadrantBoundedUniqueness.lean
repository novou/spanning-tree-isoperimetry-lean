import SpanningTreeIsoperimetry.BoundaryGreenBounds

/-! Bounded uniqueness for the killed quadrant Laplacian. The proof compares
on finite boxes with an explicit affine supersolution and lets its slope tend
to zero. It uses the checked nonnegative finite inverse, not an assumed
infinite-domain maximum principle. -/
namespace SpanningTreeIsoperimetry.QuadrantBoundedUniqueness
open Ferrers CornerEnergy BoundaryGreenBounds BoundaryGreenLoss SquareMaximality.Boundary Filter
open scoped Matrix BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem finite_nonneg_of_laplacian_nonneg {R S : ℕ} {U : Diagram}
    (hU : U⊆faceRectangle R S) (v : {p // p∈U} → ℝ)
    (hv : ∀ p,0≤(fourIminusAdjacency U*ᵥv) p) (p : {p // p∈U}) : 0≤v p := by
  have hI := Matrix.nonsing_inv_mul (fourIminusAdjacency U)
    (isUnit_iff_ne_zero.mpr (dirichlet_posDef hU).det_pos.ne')
  have hm : (fourIminusAdjacency U)⁻¹*ᵥ(fourIminusAdjacency U*ᵥv)=v := by
    rw [Matrix.mulVec_mulVec,hI,Matrix.one_mulVec]
  rw [← hm]
  apply Finset.sum_nonneg
  intro t _
  apply mul_nonneg _ (hv t)
  simpa only [green_mem p.property t.property] using green_nonneg hU p.val t.val

theorem laplacian_const_mul (c : ℝ) (f : Point → ℝ) (p : Point) :
    laplacian (fun t => c*f t) p=c*laplacian f p := by
  unfold laplacian
  split_ifs <;> ring

theorem laplacian_neg (f : Point → ℝ) (p : Point) :
    laplacian (fun t => -f t) p= -laplacian f p := by
  simpa only [neg_one_mul] using laplacian_const_mul (-1) f p

theorem extend_le_of_nonneg_outside {U : Diagram} {f : Point → ℝ}
    (hf : ∀ p,p∉U → 0≤f p) (p : Point) : extend U (fun t => f t.val) p≤f p := by
  by_cases hp : p∈U
  · simp only [extend_mem _ hp,le_refl]
  · rw [extend_not_mem _ hp]
    exact hf p hp

theorem laplacian_extend_ge {U : Diagram} {f : Point → ℝ}
    (hf : ∀ p,p∉U → 0≤f p) {p : Point} (hp : p∈U) :
    laplacian f p≤laplacian (extend U (fun t => f t.val)) p := by
  have he := extend_le_of_nonneg_outside hf (p.1+1,p.2)
  have hw := extend_le_of_nonneg_outside hf (p.1-1,p.2)
  have hn := extend_le_of_nonneg_outside hf (p.1,p.2+1)
  have hs := extend_le_of_nonneg_outside hf (p.1,p.2-1)
  unfold laplacian
  rw [extend_mem _ hp]
  split_ifs <;> linarith

def height (p : Point) : ℝ := (p.1 : ℝ)+p.2+2

theorem height_laplacian (p : Point) :
    laplacian height p=(if p.1=0 then (p.2 : ℝ)+1 else 0)+
      (if p.2=0 then (p.1 : ℝ)+1 else 0) := by
  have pred_cast (n : ℕ) : ((n-1 : ℕ) : ℝ)=if n=0 then 0 else (n : ℝ)-1 := by
    by_cases hn : n=0
    · simp [hn]
    · rw [if_neg hn,Nat.cast_sub (by omega : 1≤n),Nat.cast_one]
  rcases p with ⟨x,y⟩
  unfold laplacian height
  simp only [Prod.fst,Prod.snd,Nat.cast_add,Nat.cast_one]
  rw [pred_cast,pred_cast]
  by_cases hx : x=0 <;> by_cases hy : y=0 <;> simp [hx,hy] <;> ring

def barrier (C : ℝ) (N : ℕ) (p : Point) : ℝ := C/((N : ℝ)+1)*height p

theorem barrier_superharmonic {C : ℝ} (hC : 0≤C) (N : ℕ) (p : Point) :
    0≤laplacian (barrier C N) p := by
  change 0≤laplacian (fun t => C/((N : ℝ)+1)*height t) p
  rw [laplacian_const_mul,height_laplacian]
  apply mul_nonneg (by positivity)
  split_ifs <;> positivity

theorem barrier_ge_bound_outside {C : ℝ} (hC : 0≤C) (N : ℕ) {p : Point}
    (hp : p∉box N) : C≤barrier C N p := by
  have hp' : ¬(p.1<N+1 ∧ p.2<N+1) := by simpa only [box,mem_faceRectangle] using hp
  have hnat : N+1≤p.1+p.2+2 := by omega
  have hh : (N : ℝ)+1≤height p := by
    unfold height
    exact_mod_cast hnat
  calc
    C=C/((N : ℝ)+1)*((N : ℝ)+1) := by field_simp
    _≤C/((N : ℝ)+1)*height p := mul_le_mul_of_nonneg_left hh (by positivity)
    _=barrier C N p := rfl

/-- Finite-box linear barrier. Killed-axis terms are nonnegative, while every
omitted far-boundary neighbour has barrier at least C. -/
theorem finite_box_bound {C : ℝ} (hC : 0≤C) (f : Point → ℝ)
    (hbound : ∀ p,f p≤C) (hf : ∀ p,laplacian f p=0)
    (N : ℕ) {p : Point} (hp : p∈box N) : f p≤barrier C N p := by
  let v : {p // p∈box N} → ℝ := fun p => barrier C N p.val-f p.val
  have hout (q : Point) (hq : q∉box N) : 0≤barrier C N q-f q := by
    linarith [barrier_ge_bound_outside hC N hq,hbound q]
  have hv (q : {p // p∈box N}) : 0≤(fourIminusAdjacency (box N)*ᵥv) q := by
    rw [dirichlet_mulVec]
    have h := laplacian_extend_ge hout q.property
    rw [laplacian_sub,hf q.val,sub_zero] at h
    exact (barrier_superharmonic hC N q.val).trans h
  have h := finite_nonneg_of_laplacian_nonneg (Finset.Subset.refl (box N)) v hv ⟨p,hp⟩
  change 0≤barrier C N p-f p at h
  linarith

theorem barrier_tendsto_zero (C : ℝ) (p : Point) :
    Tendsto (fun N : ℕ => barrier C N p) atTop (𝓝 0) := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun N => by change (N : ℝ)≤(N : ℝ)+1; linarith) tendsto_natCast_atTop_atTop
  have h := (tendsto_const_nhds.div_atTop hN :
    Tendsto (fun N : ℕ => C/((N : ℝ)+1)) atTop (𝓝 0))
  simpa only [barrier,zero_mul] using h.mul_const (height p)

theorem bounded_harmonic_nonpos {C : ℝ} (hC : 0≤C) (f : Point → ℝ)
    (hbound : ∀ p,f p≤C) (hf : ∀ p,laplacian f p=0) (p : Point) : f p≤0 := by
  apply ge_of_tendsto (barrier_tendsto_zero C p)
  filter_upwards [eventually_ge_atTop (p.1+p.2)] with N hN
  exact finite_box_bound hC f hbound hf N (by rw [box,mem_faceRectangle]; omega)

/-- Every bounded harmonic function for the killed quadrant Laplacian is
zero. This is proved through finite inverse comparison and barrier decay. -/
theorem bounded_harmonic_eq_zero {C : ℝ} (hC : 0≤C) (f : Point → ℝ)
    (hbound : ∀ p,|f p|≤C) (hf : ∀ p,laplacian f p=0) (p : Point) : f p=0 := by
  have hp := bounded_harmonic_nonpos hC f (fun p => (le_abs_self _).trans (hbound p)) hf p
  have hn := bounded_harmonic_nonpos hC (fun p => -f p)
    (fun p => (neg_le_abs _).trans (hbound p))
    (fun p => by rw [laplacian_neg,hf p,neg_zero]) p
  linarith

/-- A bounded actual Poisson kernel is uniquely the finite-box exhaustion
Green function. The final image-kernel theorem will discharge both premises. -/
theorem eq_quadrantGreen_of_bounded_poisson {C : ℝ} (hC : 0≤C) (q : Point) (f : Point → ℝ)
    (hbound : ∀ p,|f p|≤C) (hf : ∀ p,laplacian f p=if p=q then 1 else 0) (p : Point) :
    f p=quadrantGreen p q := by
  have hg (t : Point) : |quadrantGreen t q|≤(q.1 : ℝ)+1 := by
    rw [abs_of_nonneg (quadrantGreen_nonneg t q)]
    exact (quadrantGreen_le_tent t q).trans (min_le_right _ _)
  have hb (t : Point) : |f t-quadrantGreen t q|≤C+((q.1 : ℝ)+1) := by
    have h := abs_sub_le (f t) (0 : ℝ) (quadrantGreen t q)
    simp only [sub_zero,zero_sub,abs_neg] at h
    linarith [hbound t,hg t]
  have hh (t : Point) : laplacian (fun x => f x-quadrantGreen x q) t=0 := by
    rw [laplacian_sub,hf t,quadrantGreen_equation,sub_self]
  have h := bounded_harmonic_eq_zero (C := C+((q.1 : ℝ)+1)) (by positivity)
    (fun t => f t-quadrantGreen t q) hb hh p
  exact sub_eq_zero.mp h

end
end SpanningTreeIsoperimetry.QuadrantBoundedUniqueness
