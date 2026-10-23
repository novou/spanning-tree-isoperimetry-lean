module

public import SpanningTreeIsoperimetry.AbsolutelySummableDeterminant
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

@[expose] public section

/-! Products of entrywise absolutely summable real kernels, with an explicit
mass bound. These kernels perturb the identity; the identity itself need
not have summable entries. -/
namespace SpanningTreeIsoperimetry.SummableKernelProduct
open AbsolutelySummableDeterminant
open scoped BigOperators
noncomputable section
abbrev Kernel := ℕ → ℕ → ℝ

def rowNorm (A : Kernel) (i : ℕ) : ℝ := ∑' k,|A i k|
def columnNorm (A : Kernel) (j : ℕ) : ℝ := ∑' k,|A k j|
def product (A B : Kernel) (i j : ℕ) : ℝ := ∑' k,A i k*B k j

theorem row_summable {A : Kernel} (hA : Summable (entryNorm A)) (i : ℕ) :
    Summable (fun k => |A i k|) := hA.prod_factor i

theorem column_summable {A : Kernel} (hA : Summable (entryNorm A)) (j : ℕ) :
    Summable (fun k => |A k j|) := hA.prod_symm.prod_factor j

theorem rowNorm_nonneg (A : Kernel) (i : ℕ) : 0≤rowNorm A i := tsum_nonneg (fun _ => abs_nonneg _)
theorem columnNorm_nonneg (A : Kernel) (j : ℕ) : 0≤columnNorm A j := tsum_nonneg (fun _ => abs_nonneg _)
theorem totalMass_nonneg (A : Kernel) : 0≤totalMass A := tsum_nonneg (fun _ => abs_nonneg _)

theorem rowNorm_summable {A : Kernel} (hA : Summable (entryNorm A)) : Summable (rowNorm A) := hA.prod

theorem columnNorm_summable {A : Kernel} (hA : Summable (entryNorm A)) : Summable (columnNorm A) := hA.prod_symm.prod

theorem tsum_rowNorm {A : Kernel} (hA : Summable (entryNorm A)) : (∑' i,rowNorm A i)=totalMass A := hA.tsum_prod.symm

theorem tsum_columnNorm {A : Kernel} (hA : Summable (entryNorm A)) : (∑' j,columnNorm A j)=totalMass A := by
  calc
    (∑' j,columnNorm A j)=(∑' p : ℕ×ℕ,entryNorm A p.swap) := hA.prod_symm.tsum_prod.symm
    _=totalMass A := (Equiv.prodComm ℕ ℕ).tsum_eq (entryNorm A)

theorem abs_le_columnNorm {A : Kernel} (hA : Summable (entryNorm A)) (k j : ℕ) :
    |A k j|≤columnNorm A j :=
  (column_summable hA j).le_tsum k (fun _ _ => abs_nonneg _)

theorem productEntry_norm_summable {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (i j : ℕ) : Summable (fun k => |A i k*B k j|) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ ((row_summable hA i).mul_right (columnNorm B j))
  intro k
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_le_columnNorm hB k j) (abs_nonneg _)

theorem productEntry_summable {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (i j : ℕ) : Summable (fun k => A i k*B k j) := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using productEntry_norm_summable hA hB i j

theorem abs_product_le {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (i j : ℕ) : |product A B i j|≤rowNorm A i*columnNorm B j := by
  have hs := productEntry_norm_summable hA hB i j
  have hn : |product A B i j|≤∑' k,|A i k*B k j| := by
    simpa only [product,Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun k => A i k*B k j) (by simpa only [Real.norm_eq_abs] using hs)
  have hb := hs.tsum_le_tsum (fun k => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le_columnNorm hB k j) (abs_nonneg _))
    ((row_summable hA i).mul_right (columnNorm B j))
  rw [tsum_mul_right] at hb
  exact hn.trans (by simpa only [Real.norm_eq_abs,rowNorm] using hb)

theorem product_summable {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) : Summable (entryNorm (product A B)) := by
  have hs := (rowNorm_summable hA).mul_of_nonneg (columnNorm_summable hB)
    (rowNorm_nonneg A) (columnNorm_nonneg B)
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun p => abs_product_le hA hB p.1 p.2) hs

theorem product_mass_le {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) : totalMass (product A B)≤totalMass A*totalMass B := by
  let r : ℕ → ℝ := rowNorm A
  let c : ℕ → ℝ := columnNorm B
  have hr : Summable r := rowNorm_summable hA
  have hc : Summable c := columnNorm_summable hB
  have hs : Summable (fun p : ℕ×ℕ => r p.1*c p.2) :=
    hr.mul_of_nonneg hc (rowNorm_nonneg A) (columnNorm_nonneg B)
  have hb : totalMass (product A B)≤∑' p : ℕ×ℕ,r p.1*c p.2 := by
    exact (product_summable hA hB).tsum_le_tsum (fun p => abs_product_le hA hB p.1 p.2) hs
  have he : (∑' p : ℕ×ℕ,r p.1*c p.2)=(∑' i,r i)*(∑' j,c j) := by
    calc
      _=∑' i,∑' j,r i*c j := hs.tsum_prod
      _=∑' i,r i*(∑' j,c j) := tsum_congr (fun i => hc.tsum_mul_left (r i))
      _=(∑' i,r i)*(∑' j,c j) := hr.tsum_mul_right _
  have he' : (∑' i,r i)*(∑' j,c j)=totalMass A*totalMass B :=
    congrArg₂ (fun x y : ℝ => x*y) (tsum_rowNorm hA) (tsum_columnNorm hB)
  exact hb.trans_eq (he.trans he')

def composePerturbation (A B : Kernel) : Kernel := fun i j => A i j+B i j+product A B i j

theorem compose_summable {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) : Summable (entryNorm (composePerturbation A B)) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ ((hA.add hB).add (product_summable hA hB))
  intro p
  exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)

theorem compose_mass_le {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) :
    totalMass (composePerturbation A B)≤totalMass A+totalMass B+totalMass A*totalMass B := by
  have hp := product_summable hA hB
  have hb := (compose_summable hA hB).tsum_le_tsum
    (fun p => (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) ((hA.add hB).add hp)
  change totalMass (composePerturbation A B)≤
    ∑' p, (entryNorm A p+entryNorm B p+entryNorm (product A B) p) at hb
  rw [Summable.tsum_add (hA.add hB) hp,Summable.tsum_add hA hB] at hb
  exact hb.trans (add_le_add le_rfl (product_mass_le hA hB))

end
end SpanningTreeIsoperimetry.SummableKernelProduct
