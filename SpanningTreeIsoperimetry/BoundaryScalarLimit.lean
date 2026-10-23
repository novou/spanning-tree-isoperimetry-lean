module

public import SpanningTreeIsoperimetry.BoundaryTridiagonalGreen

@[expose] public section

/-! The arbitrary-depth scalar half-line Green kernel is the limit of actual
finite tridiagonal inverse entries, with its exact positive boundary loss. -/
namespace SpanningTreeIsoperimetry.BoundaryScalarLimit
open BoundaryTridiagonalGreen Filter
open scoped Topology Matrix Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

/-- Explicit half-line entry (defined separately from the finite inverse). -/
def halfEntry (t : ℝ) (a b : ℕ) : ℝ :=
  Real.sinh ((((min a b : ℕ) : ℝ)+1)*t)*
    Real.exp (-((((max a b : ℕ) : ℝ)+1)*t))/Real.sinh t

theorem tridiagonal_isSymm (n : ℕ) (t : ℝ) : (tridiagonal n t).IsSymm := by
  rw [Matrix.IsSymm,tridiagonal,Matrix.transpose_sub,Matrix.transpose_smul,
    Matrix.transpose_one,(SimpleGraph.pathGraph n).isSymm_adjMatrix]

theorem kernel_symm (n : ℕ) (t : ℝ) (ht : 0<t) (i j : Fin n) : kernel n t i j=kernel n t j i := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j i) (tridiagonal_isSymm n t).inv.eq
  simpa only [Matrix.transpose_apply,inverse_eq_kernel n t ht] using h

theorem halfEntry_sub_kernel (n : ℕ) (t : ℝ) (ht : 0<t) (i j : Fin n) :
    halfEntry t i.val j.val-kernel n t i j=
      2*Real.sinh (((i.val : ℝ)+1)*t)*Real.sinh (((j.val : ℝ)+1)*t)/
        (Real.sinh t*(Real.exp (2*((n : ℝ)+1)*t)-1)) := by
  by_cases hij : i.val≤j.val
  · have h := inverse_entry_loss_of_le n t ht i j hij
    simpa only [halfEntry,min_eq_left hij,max_eq_right hij,inverse_eq_kernel n t ht] using h
  · have hji : j.val ≤ i.val := Nat.le_of_lt (Nat.lt_of_not_ge hij)
    have h := inverse_entry_loss_of_le n t ht j i hji
    rw [inverse_eq_kernel n t ht,← kernel_symm n t ht i j] at h
    unfold halfEntry
    rw [min_eq_right hji,max_eq_left hji]
    convert h using 1 <;> ring

def pathLength (N a b : ℕ) : ℕ := N+(a+b+1)

def leftSite (N a b : ℕ) : Fin (pathLength N a b) := ⟨a,by unfold pathLength; omega⟩
def rightSite (N a b : ℕ) : Fin (pathLength N a b) := ⟨b,by unfold pathLength; omega⟩

def finiteEntry (N : ℕ) (t : ℝ) (a b : ℕ) : ℝ :=
  kernel (pathLength N a b) t (leftSite N a b) (rightSite N a b)

/-- The actual finite path entry tends to the displayed half-line value. -/
theorem finiteEntry_tendsto (t : ℝ) (ht : 0<t) (a b : ℕ) :
    Tendsto (fun N => finiteEntry N t a b) atTop (𝓝 (halfEntry t a b)) := by
  have hl : Tendsto (fun N => (pathLength N a b : ℝ)) atTop atTop := by
    simpa only [pathLength,Function.comp_def] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat (a+b+1))
  have ha : Tendsto (fun N => 2*((pathLength N a b : ℝ)+1)*t) atTop atTop := by
    have hh := (hl.atTop_add (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))).const_mul_atTop
      (show 0<2*t by positivity)
    convert hh using 1
    funext N
    ring
  have hd : Tendsto (fun N => Real.exp (2*((pathLength N a b : ℝ)+1)*t)-1) atTop atTop := by
    simpa only [Function.comp_def,sub_eq_add_neg] using (Real.tendsto_exp_atTop.comp ha).atTop_add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 (-1)))
  have hz := (tendsto_const_nhds.div_atTop hd :
    Tendsto (fun N => (2*Real.sinh (((a : ℝ)+1)*t)*Real.sinh (((b : ℝ)+1)*t)/Real.sinh t)/
      (Real.exp (2*((pathLength N a b : ℝ)+1)*t)-1)) atTop (𝓝 0))
  simp only [div_div] at hz
  have h := hz.const_sub (halfEntry t a b)
  simp only [sub_zero] at h
  apply h.congr
  intro N
  have he := halfEntry_sub_kernel (pathLength N a b) t ht (leftSite N a b) (rightSite N a b)
  change halfEntry t a b-finiteEntry N t a b=_ at he
  simp only [leftSite,rightSite] at he
  linarith only [he]

end
end SpanningTreeIsoperimetry.BoundaryScalarLimit
