module

public import SpanningTreeIsoperimetry.ScalarResolvent

@[expose] public section

/-! Exact integer Dirichlet systems determine actual finite Green entries.
Concrete integer potentials are checked separately in Lean's kernel. -/
namespace SpanningTreeIsoperimetry.FixedDirichletSystems
open ScalarResolvent

def gridKernel (R S : ℕ) : Matrix (Fin R × Fin S) (Fin R × Fin S) ℤ :=
  fun p q => if p==q then 4 else
    if Nat.dist p.1.val q.1.val+Nat.dist p.2.val q.2.val==1 then -1 else 0

def selection {R S k : ℕ} (src : Fin k → Fin R × Fin S) : Matrix (Fin R × Fin S) (Fin k) ℤ :=
  fun p c => if p==src c then 1 else 0

theorem kernel_cast (R S : ℕ) :
    (gridKernel R S).map (Int.castRingHom ℝ)=rectangleDirichlet R S := by
  classical
  ext p q
  have ha : (SimpleGraph.pathGraph R □ SimpleGraph.pathGraph S).Adj p q ↔
      Nat.dist p.1.val q.1.val+Nat.dist p.2.val q.2.val=1 := by
    simp only [SimpleGraph.boxProd_adj,SimpleGraph.pathGraph_adj,Fin.ext_iff]
    unfold Nat.dist
    omega
  by_cases hpq : p=q
  · subst q
    simp [gridKernel,rectangleDirichlet_eq_grid,Matrix.map_apply,Matrix.sub_apply,
      Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,SimpleGraph.adjMatrix_apply]
  · by_cases hd : Nat.dist p.1.val q.1.val+Nat.dist p.2.val q.2.val=1
    · have hg:=ha.mpr hd
      simp only [SimpleGraph.boxProd_adj] at hg
      simp [gridKernel,rectangleDirichlet_eq_grid,Matrix.map_apply,Matrix.sub_apply,
        Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,SimpleGraph.adjMatrix_apply,hpq,hd,hg]
    · have hg : ¬(SimpleGraph.pathGraph R □ SimpleGraph.pathGraph S).Adj p q :=
        fun h => hd (ha.mp h)
      simp only [SimpleGraph.boxProd_adj] at hg
      simp [gridKernel,rectangleDirichlet_eq_grid,Matrix.map_apply,Matrix.sub_apply,
        Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,SimpleGraph.adjMatrix_apply,hpq,hd,hg]

noncomputable section

/-- Any checked integer solution yields the actual inverse columns. -/
theorem inverse_entries_of_integer_system {R S k : ℕ} (src : Fin k → Fin R × Fin S)
    (V : Matrix (Fin R × Fin S) (Fin k) ℤ) (D : ℤ) (hD : 0<D)
    (hs : ∀ p c, (gridKernel R S*V) p c=D*selection src p c) (p : Fin R × Fin S) (c : Fin k) :
    (rectangleDirichlet R S)⁻¹ p (src c)=(V p c : ℝ)/(D : ℝ) := by
  classical
  let Vr := V.map (Int.castRingHom ℝ)
  let E := (selection src).map (Int.castRingHom ℝ)
  have hcast : rectangleDirichlet R S*Vr=(D : ℝ) • E := by
    rw [← kernel_cast,← Matrix.map_mul]
    ext p c
    rw [Matrix.map_apply,hs p c]
    simp [E,Matrix.smul_apply,Matrix.map_apply,smul_eq_mul]
  have hD0 : (D : ℝ)≠0 := by exact_mod_cast (ne_of_gt hD)
  have hmul : rectangleDirichlet R S*((D : ℝ)⁻¹ • Vr)=E := by
    rw [Matrix.mul_smul,hcast,smul_smul,inv_mul_cancel₀ hD0,one_smul]
  have hinv : (rectangleDirichlet R S)⁻¹*E=(D : ℝ)⁻¹ • Vr := by
    rw [← hmul,← Matrix.mul_assoc,Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (rectangleDirichlet_posDef R S).det_pos.ne'),Matrix.one_mul]
  have h:=congrArg (fun A => A p c) hinv
  simpa [E,Vr,selection,Matrix.mul_apply,Matrix.smul_apply,Matrix.map_apply,
    smul_eq_mul,mul_ite,Finset.sum_ite_eq',div_eq_mul_inv,mul_comm] using h

end
end SpanningTreeIsoperimetry.FixedDirichletSystems
