import SpanningTreeIsoperimetry.FiniteGreenPotentials

/-! All eight finite boundary-minor floors from Appendix B, for the actual
rectangular inverse matrices. Exact integer systems replace root brackets. -/
namespace SpanningTreeIsoperimetry.FiniteBoundaryMinors
open ScalarResolvent FixedDirichletSystems FiniteGreenPotentials
noncomputable section

 def leadingBlock {R S k : ℕ} (hR : 0<R) (hk : k≤S) : Matrix (Fin k) (Fin k) ℝ :=
  (boundaryGreen hR S).submatrix (Fin.castLE hk) (Fin.castLE hk)

def potentialBlock {R S k : ℕ} (hR : 0<R) (hk : k≤S)
    (V : Matrix (Fin R × Fin S) (Fin k) ℤ) (D : ℤ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => (V (boundarySources hR hk i) j : ℝ)/(D : ℝ)

theorem leadingBlock_eq_potential {R S k : ℕ} (hR : 0<R) (hk : k≤S)
    (V : Matrix (Fin R × Fin S) (Fin k) ℤ) (D : ℤ) (hD : 0<D)
    (hs : ∀ p c, (gridKernel R S*V) p c=D*selection (boundarySources hR hk) p c) :
    leadingBlock hR hk=potentialBlock hR hk V D := by
  ext i j
  exact inverse_entries_of_integer_system (boundarySources hR hk) V D hD hs
    (boundarySources hR hk i) j

theorem block_4_6 : leadingBlock (by decide : 0<3) (by decide : 2≤5)=
    potentialBlock (by decide : 0<3) (by decide : 2≤5) potential_4_6 denominator_4_6 :=
  leadingBlock_eq_potential _ _ _ _ (by norm_num [denominator_4_6]) system_4_6

set_option maxHeartbeats 1000000 in
 theorem det_4_6 : Matrix.det (leadingBlock (by decide : 0<3) (by decide : 2≤5))=
    (3887251/42634410) := by
  rw [block_4_6]
  norm_num [Matrix.det_succ_row_zero,Fin.sum_univ_succ,Matrix.submatrix,Fin.succAbove,
    potentialBlock,potential_4_6,denominator_4_6,boundarySources]

 theorem floor_4_6 : ((9117/100000) : ℝ)<
    Matrix.det (leadingBlock (by decide : 0<3) (by decide : 2≤5)) := by
  rw [det_4_6]
  norm_num

theorem block_4_7 : leadingBlock (by decide : 0<3) (by decide : 2≤6)=
    potentialBlock (by decide : 0<3) (by decide : 2≤6) potential_4_7 denominator_4_7 :=
  leadingBlock_eq_potential _ _ _ _ (by norm_num [denominator_4_7]) system_4_7

set_option maxHeartbeats 1000000 in
 theorem det_4_7 : Matrix.det (leadingBlock (by decide : 0<3) (by decide : 2≤6))=
    (640795680/7022359583) := by
  rw [block_4_7]
  norm_num [Matrix.det_succ_row_zero,Fin.sum_univ_succ,Matrix.submatrix,Fin.succAbove,
    potentialBlock,potential_4_7,denominator_4_7,boundarySources]

 theorem floor_4_7 : ((73/800) : ℝ)<
    Matrix.det (leadingBlock (by decide : 0<3) (by decide : 2≤6)) := by
  rw [det_4_7]
  norm_num

theorem block_5_7 : leadingBlock (by decide : 0<4) (by decide : 2≤6)=
    potentialBlock (by decide : 0<4) (by decide : 2≤6) potential_5_7 denominator_5_7 :=
  leadingBlock_eq_potential _ _ _ _ (by norm_num [denominator_5_7]) system_5_7

set_option maxHeartbeats 1000000 in
 theorem det_5_7 : Matrix.det (leadingBlock (by decide : 0<4) (by decide : 2≤6))=
    (924878446848/10021992194369) := by
  rw [block_5_7]
  norm_num [Matrix.det_succ_row_zero,Fin.sum_univ_succ,Matrix.submatrix,Fin.succAbove,
    potentialBlock,potential_5_7,denominator_5_7,boundarySources]

 theorem floor_5_7 : ((2307/25000) : ℝ)<
    Matrix.det (leadingBlock (by decide : 0<4) (by decide : 2≤6)) := by
  rw [det_5_7]
  norm_num

theorem block_5_8 : leadingBlock (by decide : 0<4) (by decide : 3≤7)=
    potentialBlock (by decide : 0<4) (by decide : 3≤7) potential_5_8 denominator_5_8 :=
  leadingBlock_eq_potential _ _ _ _ (by norm_num [denominator_5_8]) system_5_8

set_option maxHeartbeats 1000000 in
 theorem det_5_8 : Matrix.det (leadingBlock (by decide : 0<4) (by decide : 3≤7))=
    (3459364930672/122038315192179) := by
  rw [block_5_8]
  norm_num [Matrix.det_succ_row_zero,Fin.sum_univ_succ,Matrix.submatrix,Fin.succAbove,
    potentialBlock,potential_5_8,denominator_5_8,boundarySources]

 theorem floor_5_8 : ((14173/500000) : ℝ)<
    Matrix.det (leadingBlock (by decide : 0<4) (by decide : 3≤7)) := by
  rw [det_5_8]
  norm_num

theorem block_6_10 : leadingBlock (by decide : 0<5) (by decide : 3≤9)=
    potentialBlock (by decide : 0<5) (by decide : 3≤9) potential_6_10 denominator_6_10 :=
  leadingBlock_eq_potential _ _ _ _ (by norm_num [denominator_6_10]) system_6_10

set_option maxHeartbeats 1000000 in
 theorem det_6_10 : Matrix.det (leadingBlock (by decide : 0<5) (by decide : 3≤9))=
    (33020184551399274034159/1154617875754582889149500) := by
  rw [block_6_10]
  norm_num [Matrix.det_succ_row_zero,Fin.sum_univ_succ,Matrix.submatrix,Fin.succAbove,
    potentialBlock,potential_6_10,denominator_6_10,boundarySources]

 theorem floor_6_10 : ((5719/200000) : ℝ)<
    Matrix.det (leadingBlock (by decide : 0<5) (by decide : 3≤9)) := by
  rw [det_6_10]
  norm_num

theorem block_7_11 : leadingBlock (by decide : 0<6) (by decide : 4≤10)=
    potentialBlock (by decide : 0<6) (by decide : 4≤10) potential_7_11 denominator_7_11 :=
  leadingBlock_eq_potential _ _ _ _ (by norm_num [denominator_7_11]) system_7_11

set_option maxHeartbeats 1000000 in
 theorem det_7_11 : Matrix.det (leadingBlock (by decide : 0<6) (by decide : 4≤10))=
    (681081413480015620350952302400/76692291658239649098972455530913) := by
  rw [block_7_11]
  norm_num [Matrix.det_succ_row_zero,Fin.sum_univ_succ,Matrix.submatrix,Fin.succAbove,
    potentialBlock,potential_7_11,denominator_7_11,boundarySources]

 theorem floor_7_11 : ((111/12500) : ℝ)<
    Matrix.det (leadingBlock (by decide : 0<6) (by decide : 4≤10)) := by
  rw [det_7_11]
  norm_num

theorem block_8_12 : leadingBlock (by decide : 0<7) (by decide : 4≤11)=
    potentialBlock (by decide : 0<7) (by decide : 4≤11) potential_8_12 denominator_8_12 :=
  leadingBlock_eq_potential _ _ _ _ (by norm_num [denominator_8_12]) system_8_12

set_option maxHeartbeats 1000000 in
 theorem det_8_12 : Matrix.det (leadingBlock (by decide : 0<7) (by decide : 4≤11))=
    (1290001224286084268249567525357573413/144765033382068903168240004424877281280) := by
  rw [block_8_12]
  norm_num [Matrix.det_succ_row_zero,Fin.sum_univ_succ,Matrix.submatrix,Fin.succAbove,
    potentialBlock,potential_8_12,denominator_8_12,boundarySources]

 theorem floor_8_12 : ((891/100000) : ℝ)<
    Matrix.det (leadingBlock (by decide : 0<7) (by decide : 4≤11)) := by
  rw [det_8_12]
  norm_num

theorem singleton_4_6 : (30013 : ℝ)/100000<
    Matrix.det (leadingBlock (by decide : 0<3) (by decide : 1≤5)) := by
  rw [Matrix.det_fin_one]
  have h := congrFun (congrFun block_4_6 (0 : Fin 2)) (0 : Fin 2)
  change (boundaryGreen (by decide : 0<3) 5) 0 0=_ at h
  norm_num [potentialBlock,potential_4_6,denominator_4_6,boundarySources] at h
  change (30013 : ℝ)/100000<(boundaryGreen (by decide : 0<3) 5) 0 0
  rw [h]
  norm_num

end
end SpanningTreeIsoperimetry.FiniteBoundaryMinors
