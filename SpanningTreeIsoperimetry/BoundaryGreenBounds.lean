module

public import SpanningTreeIsoperimetry.BoundaryGreenLoss
public import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section

/-! A discrete supersolution bounds every actual finite Green entry. -/
namespace SpanningTreeIsoperimetry.BoundaryGreenBounds
open Ferrers CornerEnergy BoundaryGreenLoss SquareMaximality.Boundary
open scoped BigOperators Classical Matrix Topology
open Filter
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def tent (q : ℕ) (p : Point) : ℝ := min ((p.1 : ℝ)+1) ((q : ℝ)+1)

theorem tent_nonneg (q : ℕ) (p : Point) : 0≤tent q p := by unfold tent; positivity

theorem extend_tent_le (U : Diagram) (q : ℕ) (p : Point) :
    extend U (fun t => tent q t.val) p≤tent q p := by
  by_cases hp : p∈U
  · simp only [extend_mem _ hp,le_refl]
  · rw [extend_not_mem _ hp]
    exact tent_nonneg q p

theorem tent_second_difference (x q : ℕ) :
    2*min ((x : ℝ)+1) ((q : ℝ)+1)-min ((x : ℝ)+2) ((q : ℝ)+1)-
      min (x : ℝ) ((q : ℝ)+1) = if x=q then 1 else 0 := by
  rcases lt_trichotomy x q with h | h | h
  · have hx : (x : ℝ)+1≤q := by exact_mod_cast (show x+1≤q by omega)
    have hne : x≠q := ne_of_lt h
    rw [min_eq_left (by linarith),min_eq_left (by linarith),min_eq_left (by linarith),if_neg hne]
    ring
  · subst q
    rw [min_self,min_eq_right (by linarith),min_eq_left (by linarith),if_pos rfl]
    ring
  · have hx : (q : ℝ)+1≤x := by exact_mod_cast (show q+1≤x by omega)
    have hne : x≠q := ne_of_gt h
    rw [min_eq_right (by linarith),min_eq_right (by linarith),min_eq_right hx,if_neg hne]
    ring

theorem tent_supersolution (U : Diagram) (p q : {p // p∈U}) :
    (if p=q then (1 : ℝ) else 0)≤(fourIminusAdjacency U *ᵥ (fun t => tent q.val.1 t.val)) p := by
  rw [dirichlet_mulVec]
  have hr := extend_tent_le U q.val.1 (p.val.1+1,p.val.2)
  have hu := extend_tent_le U q.val.1 (p.val.1,p.val.2+1)
  have hl : (if p.val.1=0 then (0 : ℝ) else
      extend U (fun t => tent q.val.1 t.val) (p.val.1-1,p.val.2))≤
      min (p.val.1 : ℝ) ((q.val.1 : ℝ)+1) := by
    by_cases hx : p.val.1=0
    · simp [hx]
      positivity
    · have h := extend_tent_le U q.val.1 (p.val.1-1,p.val.2)
      have he : ((p.val.1-1 : ℕ) : ℝ)+1=(p.val.1 : ℝ) := by
        rw [Nat.cast_sub (by omega : 1≤p.val.1)]
        norm_num
      simpa only [hx,ite_false,tent,Prod.fst,he] using h
  have hd : (if p.val.2=0 then (0 : ℝ) else
      extend U (fun t => tent q.val.1 t.val) (p.val.1,p.val.2-1))≤tent q.val.1 p.val := by
    by_cases hy : p.val.2=0
    · simp only [hy,ite_true]
      exact tent_nonneg _ _
    · simpa only [hy,ite_false,tent,Prod.fst] using
        extend_tent_le U q.val.1 (p.val.1,p.val.2-1)
  have he := tent_second_difference p.val.1 q.val.1
  have hδ : (if p=q then (1 : ℝ) else 0)≤(if p.val.1=q.val.1 then 1 else 0) := by
    by_cases hpq : p=q
    · subst q; simp
    · simp only [hpq,ite_false]
      split_ifs <;> norm_num
  simp only [tent,Prod.fst,Nat.cast_add,Nat.cast_one] at hr hu hl hd
  rw [show ((p.val.1 : ℝ)+1+1)=((p.val.1 : ℝ)+2) by ring] at hr
  simp only [laplacian,extend_mem _ p.property,tent]
  linarith

/-- Any nonnegative finite Green inverse transports a point-source
supersolution into an upper bound for each actual inverse entry. -/
theorem inverse_le_supersolution {R S : ℕ} {U : Diagram} (hU : U⊆faceRectangle R S)
    (v : {p // p∈U} → ℝ) (q : {p // p∈U})
    (hv : ∀ t : {p // p∈U}, (if t=q then (1 : ℝ) else 0)≤(fourIminusAdjacency U *ᵥ v) t)
    (p : {p // p∈U}) : (fourIminusAdjacency U)⁻¹ p q≤v p := by
  have hI := Matrix.nonsing_inv_mul (fourIminusAdjacency U)
    (isUnit_iff_ne_zero.mpr (dirichlet_posDef hU).det_pos.ne')
  have hm : ((fourIminusAdjacency U)⁻¹ *ᵥ (fourIminusAdjacency U *ᵥ v))=v := by
    rw [Matrix.mulVec_mulVec,hI,Matrix.one_mulVec]
  calc
    _ = ∑ t : {p // p∈U}, (fourIminusAdjacency U)⁻¹ p t*(if t=q then (1 : ℝ) else 0) := by simp
    _ ≤ ∑ t : {p // p∈U}, (fourIminusAdjacency U)⁻¹ p t*((fourIminusAdjacency U *ᵥ v) t) := by
      apply Finset.sum_le_sum
      intro t _
      apply mul_le_mul_of_nonneg_left (hv t)
      simpa only [green_mem p.property t.property] using green_nonneg hU p.val t.val
    _ = v p := congrFun hm p

/-- A uniform entrywise bound independent of the size and shape of the finite
domain. It supplies actual quadrant entry limits without assuming a kernel. -/
theorem green_le_tent {R S : ℕ} {U : Diagram} (hU : U⊆faceRectangle R S) (p q : Point) :
    green U p q≤min ((p.1 : ℝ)+1) ((q.1 : ℝ)+1) := by
  by_cases hp : p∈U
  · by_cases hq : q∈U
    · rw [green_mem hp hq]
      exact inverse_le_supersolution hU (fun t => tent q.1 t.val) ⟨q,hq⟩
        (fun t => tent_supersolution U t ⟨q,hq⟩) ⟨p,hp⟩
    · simp only [green,hp,hq,dite_true,dite_false]
      positivity
  · simp only [green,hp,dite_false]
    positivity

open FaceWalkWords

def includePoint {U V : Diagram} (hUV : U⊆V) (p : {p // p∈U}) : {p // p∈V} :=
  ⟨p.val,hUV p.property⟩

def includeWord {U V : Diagram} (hUV : U⊆V) (p q : {p // p∈U}) (n : ℕ)
    (w : EndpointWord U p q n) : EndpointWord V (includePoint hUV p) (includePoint hUV q) n :=
  ⟨w.val,by
    constructor
    · exact w.property.1
    · intro t ht
      obtain ⟨a,ha⟩ := w.property.2 t ht
      exact ⟨includePoint hUV a,ha⟩⟩

theorem includeWord_injective {U V : Diagram} (hUV : U⊆V) (p q : {p // p∈U}) (n : ℕ) :
    Function.Injective (includeWord hUV p q n) := by
  intro w v h
  apply Subtype.ext
  exact congrArg (fun z : EndpointWord V (includePoint hUV p) (includePoint hUV q) n => z.val) h

/-- Ambient enlargement increases each actual Green entry, proved by the
literal inclusion of fixed-length endpoint words. -/
theorem green_mono {R S T W : ℕ} {U V : Diagram}
    (hU : U⊆faceRectangle R S) (hV : V⊆faceRectangle T W) (hUV : U⊆V) (p q : Point) :
    green U p q≤green V p q := by
  by_cases hp : p∈U
  · by_cases hq : q∈U
    · let pU : {p // p∈U} := ⟨p,hp⟩
      let qU : {p // p∈U} := ⟨q,hq⟩
      have hsU := MatrixGreenSeries.face_inverse_walk_hasSum ((foundation_faceIndices R S).symm ▸ hU) pU qU
      have hsV := MatrixGreenSeries.face_inverse_walk_hasSum ((foundation_faceIndices T W).symm ▸ hV)
        (includePoint hUV pU) (includePoint hUV qU)
      have hc (n : ℕ) :
          (Fintype.card {w : (faceGraph U).Walk pU qU // w.length=n} : ℝ)/4^(n+1)≤
          (Fintype.card {w : (faceGraph V).Walk (includePoint hUV pU) (includePoint hUV qU) //
            w.length=n} : ℝ)/4^(n+1) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [Fintype.card_congr (endpointWordEquiv U pU qU n),
          Fintype.card_congr (endpointWordEquiv V (includePoint hUV pU) (includePoint hUV qU) n)]
        exact_mod_cast Fintype.card_le_of_injective _ (includeWord_injective hUV pU qU n)
      simpa only [green_mem hp hq,green_mem (hUV hp) (hUV hq),includePoint,pU,qU] using hasSum_le hc hsU hsV
    · simp only [green,hp,hq,dite_true,dite_false]
      exact green_nonneg hV p q
  · rw [green, dif_neg hp]
    exact green_nonneg hV p q

theorem loss_nonneg {R S T W : ℕ} {U V : Diagram}
    (hU : U⊆faceRectangle R S) (hV : V⊆faceRectangle T W) (hUV : U⊆V) (p q : Point) :
    0≤loss U V p q := sub_nonneg.mpr (green_mono hU hV hUV p q)

/-- Canonical exhaustion of the quadrant by actual finite squares. -/
def box (N : ℕ) : Diagram := faceRectangle (N+1) (N+1)

def quadrantGreen (p q : Point) : ℝ := ⨆ N : ℕ, green (box N) p q

theorem box_green_monotone (p q : Point) : Monotone (fun N => green (box N) p q) := by
  intro N M hNM
  exact green_mono (Finset.Subset.refl _) (Finset.Subset.refl _)
    (FiniteGreenMonotonicity.rectangle_subset (by omega : N+1≤M+1) (by omega)) p q

theorem box_green_bddAbove (p q : Point) : BddAbove (Set.range (fun N => green (box N) p q)) := by
  refine ⟨min ((p.1 : ℝ)+1) ((q.1 : ℝ)+1),?_⟩
  rintro _ ⟨N,rfl⟩
  exact green_le_tent (Finset.Subset.refl _) p q

/-- Every actual quadrant inverse entry exists, with no Fourier kernel or
external Green theorem assumed. -/
theorem green_tendsto_quadrant (p q : Point) :
    Filter.Tendsto (fun N => green (box N) p q) Filter.atTop (𝓝 (quadrantGreen p q)) :=
  tendsto_atTop_ciSup (box_green_monotone p q) (box_green_bddAbove p q)

theorem finite_green_le_quadrant {R S : ℕ} {U : Diagram} (hU : U⊆faceRectangle R S) (p q : Point) :
    green U p q≤quadrantGreen p q := by
  have hUbox : U⊆box (R+S) := hU.trans (FiniteGreenMonotonicity.rectangle_subset (by omega) (by omega))
  exact (green_mono hU (Finset.Subset.refl _) hUbox p q).trans
    (le_ciSup (box_green_bddAbove p q) (R+S))

theorem green_symm {R S : ℕ} {U : Diagram} (hU : U⊆faceRectangle R S) (p q : Point) :
    green U p q=green U q p := by
  by_cases hp : p∈U
  · by_cases hq : q∈U
    · rw [green_mem hp hq,green_mem hq hp]
      simpa only [star_trivial] using ((dirichlet_posDef hU).isHermitian.inv.apply ⟨q,hq⟩ ⟨p,hp⟩)
    · simp [green,hp,hq]
  · simp [green,hp]

theorem quadrantGreen_symm (p q : Point) : quadrantGreen p q=quadrantGreen q p := by
  apply tendsto_nhds_unique (green_tendsto_quadrant p q)
  exact (green_tendsto_quadrant q p).congr
    (fun N => (green_symm (Finset.Subset.refl (box N)) p q).symm)

theorem quadrantGreen_nonneg (p q : Point) : 0≤quadrantGreen p q :=
  (green_nonneg (Finset.Subset.refl (box 0)) p q).trans
    (le_ciSup (box_green_bddAbove p q) 0)

theorem quadrantGreen_le_tent (p q : Point) :
    quadrantGreen p q≤min ((p.1 : ℝ)+1) ((q.1 : ℝ)+1) :=
  ciSup_le (fun N => green_le_tent (Finset.Subset.refl (box N)) p q)

theorem quadrantGreen_equation (p q : Point) :
    laplacian (fun t => quadrantGreen t q) p=if p=q then 1 else 0 := by
  have hl : Tendsto (fun N => if p.1=0 then (0 : ℝ) else green (box N) (p.1-1,p.2) q)
      atTop (𝓝 (if p.1=0 then 0 else quadrantGreen (p.1-1,p.2) q)) := by
    by_cases hx : p.1=0
    · simpa only [hx,ite_true] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · simpa only [hx,ite_false] using green_tendsto_quadrant (p.1-1,p.2) q
  have hd : Tendsto (fun N => if p.2=0 then (0 : ℝ) else green (box N) (p.1,p.2-1) q)
      atTop (𝓝 (if p.2=0 then 0 else quadrantGreen (p.1,p.2-1) q)) := by
    by_cases hy : p.2=0
    · simpa only [hy,ite_true] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · simpa only [hy,ite_false] using green_tendsto_quadrant (p.1,p.2-1) q
  have hlim : Tendsto (fun N => laplacian (fun t => green (box N) t q) p) atTop
      (𝓝 (laplacian (fun t => quadrantGreen t q) p)) :=
    (((((green_tendsto_quadrant p q).const_mul 4).sub
      (green_tendsto_quadrant (p.1+1,p.2) q)).sub hl).sub
      (green_tendsto_quadrant (p.1,p.2+1) q)).sub hd
  apply tendsto_nhds_unique hlim
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (p.1+p.2+q.1+q.2)] with N hN
  symm
  apply green_equation (Finset.Subset.refl (box N))
  · rw [box,mem_faceRectangle]
    omega
  · rw [box,mem_faceRectangle]
    omega

def quadrantLoss (U : Diagram) (p q : Point) : ℝ := quadrantGreen p q-green U p q

theorem quadrantLoss_nonneg {R S : ℕ} {U : Diagram}
    (hU : U⊆faceRectangle R S) (p q : Point) : 0≤quadrantLoss U p q :=
  sub_nonneg.mpr (finite_green_le_quadrant hU p q)

theorem quadrantLoss_harmonic {R S : ℕ} {U : Diagram}
    (hU : U⊆faceRectangle R S) {p q : Point} (hp : p∈U) (hq : q∈U) :
    laplacian (fun t => quadrantLoss U t q) p=0 := by
  change laplacian (fun t => quadrantGreen t q-green U t q) p=0
  rw [laplacian_sub,quadrantGreen_equation,green_equation hU hp hq]
  exact sub_self _

end
end SpanningTreeIsoperimetry.BoundaryGreenBounds
