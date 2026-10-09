import SpanningTreeIsoperimetry.RegularizedGreenSeries

/-! Actual finite-box exhaustion and Poisson equation for the regularized
quadrant Green kernel. Every finite entry is a genuine matrix inverse. -/
namespace SpanningTreeIsoperimetry.RegularizedQuadrantGreen
open Ferrers CornerEnergy BoundaryGreenLoss BoundaryGreenBounds RegularizedGreenSeries
open FaceWalkWords SquareMaximality.Boundary Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def laplacianZ (z : ℝ) (f : Point → ℝ) (p : Point) : ℝ := (z-4)*f p+laplacian f p

theorem laplacianZ_explicit (z : ℝ) (f : Point → ℝ) (p : Point) :
    laplacianZ z f p=z*f p-f (p.1+1,p.2)-(if p.1=0 then 0 else f (p.1-1,p.2))-
      f (p.1,p.2+1)-(if p.2=0 then 0 else f (p.1,p.2-1)) := by
  unfold laplacianZ laplacian
  ring

theorem laplacianZ_sub (z : ℝ) (f g : Point → ℝ) (p : Point) :
    laplacianZ z (fun t => f t-g t) p=laplacianZ z f p-laplacianZ z g p := by
  unfold laplacianZ
  rw [laplacian_sub]
  ring

theorem dirichletZ_eq (z : ℝ) (U : Diagram) :
    dirichletZ z U=(z-4) • (1 : Matrix {p // p∈U} {p // p∈U} ℝ)+fourIminusAdjacency U := by
  ext i j
  simp only [dirichletZ,fourIminusAdjacency,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem dirichletZ_mulVec (z : ℝ) (U : Diagram) (f : {p // p∈U} → ℝ) (p : {p // p∈U}) :
    (dirichletZ z U*ᵥf) p=laplacianZ z (extend U f) p.val := by
  rw [dirichletZ_eq,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [dirichlet_mulVec]
  simp only [laplacianZ,extend_mem f p.property]

theorem greenZ_eq_extend {z : ℝ} {U : Diagram} {q : Point} (hq : q∈U) :
    (fun p => greenZ z U p q)=extend U (fun p => (dirichletZ z U)⁻¹ p ⟨q,hq⟩) := by
  funext p
  simp [greenZ,extend,hq]

theorem greenZ_equation {z : ℝ} (hz : 4≤z) {R S : ℕ} {U : Diagram}
    (hU : U⊆faceRectangle R S) {p q : Point} (hp : p∈U) (hq : q∈U) :
    laplacianZ z (fun t => greenZ z U t q) p=if p=q then 1 else 0 := by
  rw [greenZ_eq_extend hq,← dirichletZ_mulVec z U _ ⟨p,hp⟩]
  have h := congrArg (fun A => A ⟨p,hp⟩ ⟨q,hq⟩)
    (Matrix.mul_nonsing_inv (dirichletZ z U) (isUnit_iff_ne_zero.mpr (dirichletZ_det_pos hz hU).ne'))
  simpa only [Matrix.mulVec,dotProduct,Matrix.mul_apply,Matrix.one_apply,Subtype.ext_iff] using h

theorem walk_count_le_four_pow (U : Diagram) (p q : {p // p∈U}) (n : ℕ) :
    Fintype.card {w : (faceGraph U).Walk p q // w.length=n}≤4^n := by
  rw [Fintype.card_congr (endpointWordEquiv U p q n)]
  have h := Fintype.card_subtype_le
    (fun w : SquareMaximality.ClosedWalk.Word n =>
      SquareMaximality.ClosedWalk.total w=latticePointToPoint q-latticePointToPoint p ∧ StaysIn U p w)
  have hc : Fintype.card SquareMaximality.ClosedWalk.Step=4 := by decide
  simpa only [SquareMaximality.ClosedWalk.Word,Fintype.card_fun,Fintype.card_fin,hc] using h

theorem greenZ_uniform_bound {z : ℝ} (hz : 4<z) {R S : ℕ} {U : Diagram}
    (hU : U⊆faceRectangle R S) (p q : Point) : greenZ z U p q≤1/(z-4) := by
  have hz0 : 0<z := by linarith
  by_cases hp : p∈U
  · by_cases hq : q∈U
    · have hZ := face_inverse_walk_hasSum hz.le hU ⟨p,hp⟩ ⟨q,hq⟩
      have hgeom := eigenvalue_hasSum (x := 4) hz0 (by simpa only [abs_of_pos (by norm_num : (0 : ℝ)<4)] using hz)
      have hc (n : ℕ) :
          (Fintype.card {w : (faceGraph U).Walk ⟨p,hp⟩ ⟨q,hq⟩ // w.length=n} : ℝ)/z^(n+1)≤
            4^n/z^(n+1) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast walk_count_le_four_pow U ⟨p,hp⟩ ⟨q,hq⟩ n
      simpa only [greenZ_mem hp hq,one_div] using hasSum_le hc hZ hgeom
    · simp only [greenZ,hp,hq,dite_true,dite_false]
      positivity
  · simp only [greenZ,hp,dite_false]
    positivity

theorem greenZ_mono {z : ℝ} (hz : 4≤z) {R S T W : ℕ} {U V : Diagram}
    (hU : U⊆faceRectangle R S) (hV : V⊆faceRectangle T W) (hUV : U⊆V) (p q : Point) :
    greenZ z U p q≤greenZ z V p q := by
  have hz0 : 0<z := by linarith
  by_cases hp : p∈U
  · by_cases hq : q∈U
    · let pU : {p // p∈U} := ⟨p,hp⟩
      let qU : {p // p∈U} := ⟨q,hq⟩
      have hSU := face_inverse_walk_hasSum hz hU pU qU
      have hSV := face_inverse_walk_hasSum hz hV (includePoint hUV pU) (includePoint hUV qU)
      have hc (n : ℕ) :
          (Fintype.card {w : (faceGraph U).Walk pU qU // w.length=n} : ℝ)/z^(n+1)≤
          (Fintype.card {w : (faceGraph V).Walk (includePoint hUV pU) (includePoint hUV qU) // w.length=n} : ℝ)/z^(n+1) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [Fintype.card_congr (endpointWordEquiv U pU qU n),
          Fintype.card_congr (endpointWordEquiv V (includePoint hUV pU) (includePoint hUV qU) n)]
        exact_mod_cast Fintype.card_le_of_injective _ (includeWord_injective hUV pU qU n)
      simpa only [greenZ_mem hp hq,greenZ_mem (hUV hp) (hUV hq),includePoint,pU,qU] using hasSum_le hc hSU hSV
    · simp only [greenZ,hp,hq,dite_true,dite_false]
      exact greenZ_nonneg hz hV p q
  · rw [greenZ,dif_neg hp]
    exact greenZ_nonneg hz hV p q

def quadrantGreenZ (z : ℝ) (p q : Point) : ℝ := ⨆ N : ℕ,greenZ z (box N) p q

theorem box_greenZ_monotone {z : ℝ} (hz : 4≤z) (p q : Point) :
    Monotone (fun N => greenZ z (box N) p q) := by
  intro N M hNM
  exact greenZ_mono hz (Finset.Subset.refl _) (Finset.Subset.refl _)
    (FiniteGreenMonotonicity.rectangle_subset (by omega : N+1≤M+1) (by omega)) p q

theorem box_greenZ_bddAbove {z : ℝ} (hz : 4≤z) (p q : Point) :
    BddAbove (Set.range (fun N => greenZ z (box N) p q)) := by
  refine ⟨min ((p.1 : ℝ)+1) ((q.1 : ℝ)+1),?_⟩
  rintro x ⟨N,rfl⟩
  exact greenZ_le_tent hz (Finset.Subset.refl (box N)) p q

theorem greenZ_tendsto_quadrant {z : ℝ} (hz : 4≤z) (p q : Point) :
    Tendsto (fun N => greenZ z (box N) p q) atTop (𝓝 (quadrantGreenZ z p q)) :=
  tendsto_atTop_ciSup (box_greenZ_monotone hz p q) (box_greenZ_bddAbove hz p q)

theorem quadrantGreenZ_nonneg {z : ℝ} (hz : 4≤z) (p q : Point) : 0≤quadrantGreenZ z p q :=
  (greenZ_nonneg hz (Finset.Subset.refl (box 0)) p q).trans
    (le_ciSup (box_greenZ_bddAbove hz p q) 0)

theorem quadrantGreenZ_uniform_bound {z : ℝ} (hz : 4<z) (p q : Point) :
    quadrantGreenZ z p q≤1/(z-4) :=
  ciSup_le (fun N => greenZ_uniform_bound hz (Finset.Subset.refl (box N)) p q)

theorem quadrantGreenZ_le_critical {z : ℝ} (hz : 4≤z) (p q : Point) :
    quadrantGreenZ z p q≤quadrantGreen p q := by
  apply ciSup_le
  intro N
  exact (greenZ_le_critical hz (Finset.Subset.refl (box N)) p q).trans
    (finite_green_le_quadrant (Finset.Subset.refl (box N)) p q)

theorem quadrantGreenZ_four (p q : Point) : quadrantGreenZ 4 p q=quadrantGreen p q := by
  simp only [quadrantGreenZ,greenZ_four,quadrantGreen]

/-- The actual exhausted resolvent solves the killed-quadrant Poisson equation. -/
theorem quadrantGreenZ_equation {z : ℝ} (hz : 4≤z) (p q : Point) :
    laplacianZ z (fun t => quadrantGreenZ z t q) p=if p=q then 1 else 0 := by
  have hl : Tendsto (fun N => if p.1=0 then (0 : ℝ) else greenZ z (box N) (p.1-1,p.2) q)
      atTop (𝓝 (if p.1=0 then 0 else quadrantGreenZ z (p.1-1,p.2) q)) := by
    by_cases hx : p.1=0
    · simpa only [hx,ite_true] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · simpa only [hx,ite_false] using greenZ_tendsto_quadrant hz (p.1-1,p.2) q
  have hd : Tendsto (fun N => if p.2=0 then (0 : ℝ) else greenZ z (box N) (p.1,p.2-1) q)
      atTop (𝓝 (if p.2=0 then 0 else quadrantGreenZ z (p.1,p.2-1) q)) := by
    by_cases hy : p.2=0
    · simpa only [hy,ite_true] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · simpa only [hy,ite_false] using greenZ_tendsto_quadrant hz (p.1,p.2-1) q
  have hlim : Tendsto (fun N => laplacianZ z (fun t => greenZ z (box N) t q) p) atTop
      (𝓝 (laplacianZ z (fun t => quadrantGreenZ z t q) p)) := by
    simp only [laplacianZ_explicit]
    exact (((((greenZ_tendsto_quadrant hz p q).const_mul z).sub
      (greenZ_tendsto_quadrant hz (p.1+1,p.2) q)).sub hl).sub
      (greenZ_tendsto_quadrant hz (p.1,p.2+1) q)).sub hd
  apply tendsto_nhds_unique hlim
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (p.1+p.2+q.1+q.2)] with N hN
  symm
  apply greenZ_equation hz (Finset.Subset.refl (box N))
  · rw [box,mem_faceRectangle]
    omega
  · rw [box,mem_faceRectangle]
    omega

end
end SpanningTreeIsoperimetry.RegularizedQuadrantGreen
