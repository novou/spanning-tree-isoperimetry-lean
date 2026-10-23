module

public import SpanningTreeIsoperimetry.JacobiPolynomials
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

/-! Algebraic initial-jump and terminal-rank facts for modular Hankel
computation. The successive noninitial degree-jump identity remains separate. -/
namespace SpanningTreeIsoperimetry.HankelDegreeJump

open scoped BigOperators Matrix Classical
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type*} [CommRing K]

def momentMatrix (m : ℕ → K) (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  fun i j => m (i.1 + j.1)

/-- Initial zero moments force all smaller nonempty Hankel determinants to vanish. -/
theorem det_zero_before_first (m : ℕ → K) {d t : ℕ}
    (hz : ∀ n < d, m n = 0) (ht : 0 < t) (htd : t ≤ d) :
    (momentMatrix m t).det = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero (⟨0, ht⟩ : Fin t)
  intro j
  simpa only [momentMatrix, Fin.val_mk, Nat.zero_add] using hz j.1 (j.2.trans_le htd)

/-- The first nonzero-sized Hankel block is anti-triangular; the sign is
proved by successive Laplace expansions, in arbitrary characteristic. -/
theorem initial_jump_det (m : ℕ → K) (d : ℕ) (hz : ∀ n < d, m n = 0) :
    (momentMatrix m (d + 1)).det = (-1 : K) ^ ((d + 1).choose 2) * m d ^ (d + 1) := by
  induction d generalizing m with
  | zero => simp [momentMatrix, Matrix.det_fin_one]
  | succ d ih =>
    have hm : (momentMatrix m (d + 2)).submatrix Fin.succ (Fin.last (d + 1)).succAbove =
        momentMatrix (fun n => m (n + 1)) (d + 1) := by
      ext i j
      simp [momentMatrix, Matrix.submatrix_apply, Fin.succAbove_last, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
    have hz' : ∀ n < d, m (n + 1) = 0 := by intro n hn; exact hz _ (by omega)
    rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last (d + 1))]
    · have hentry : momentMatrix m (d + 2) 0 (Fin.last (d + 1)) = m (d + 1) := by
        simp [momentMatrix]
      rw [hentry]
      simp only [Fin.val_last]
      change (-1 : K) ^ (d + 1) * m (d + 1) *
          ((momentMatrix m (d + 2)).submatrix Fin.succ (Fin.last (d + 1)).succAbove).det = _
      rw [hm, ih _ hz']
      have hc : (d + 2).choose 2 = (d + 1) + (d + 1).choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      rw [hc, pow_add (-1 : K) (d + 1) ((d + 1).choose 2),
        pow_succ' (m (d + 1)) (d + 1)]
      ring
    · intro j _ hj
      have hlt : j.1 < d + 1 := by
        have hne : j.1 ≠ d + 1 := fun h => hj (Fin.ext h)
        have := j.2
        omega
      simp [momentMatrix, hz _ hlt]
    · simp

/-- Manuscript normalization of the initial jump. -/
theorem initial_jump_det_div (m : ℕ → K) (d : ℕ) (hz : ∀ n < d, m n = 0) :
    (momentMatrix m (d + 1)).det =
      (-1 : K) ^ ((d + 1) * d / 2) * m d ^ (d + 1) := by
  simpa only [Nat.choose_two_right, Nat.add_sub_cancel] using initial_jump_det m d hz

/-- An order-d moment recurrence gives an explicit right-kernel vector in
every larger Hankel matrix. The pivot is 1, so this works over any commutative
ring and in particular over every finite field. -/
theorem det_zero_of_recurrence (m : ℕ → K) (d : ℕ) (c : Fin d → K)
    (hrec : ∀ n, m (n + d) = ∑ j : Fin d, c j * m (n + j.1))
    {k : ℕ} (hdk : d < k) : (momentMatrix m k).det = 0 := by
  let e : Fin d → Fin k := Fin.castLE hdk.le
  let p : Fin k := ⟨d, hdk⟩
  let v : Fin k → K := Pi.single p 1 - ∑ j : Fin d, c j • Pi.single (e j) 1
  have hMv : momentMatrix m k *ᵥ v = 0 := by
    dsimp only [v]
    rw [Matrix.mulVec_sub, Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul, Matrix.mulVec_single_one]
    ext i
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, Matrix.col_apply, momentMatrix]
    exact sub_eq_zero.mpr (hrec i.1)
  have hne (j : Fin d) : e j ≠ p := by
    intro h
    have hv := congrArg Fin.val h
    change j.1 = d at hv
    have := j.2
    omega
  have hvp : v p = 1 := by
    simp [v, Pi.single_apply, hne]
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hMv (i := p)
  rw [hvp]
  exact one_mem _

end SpanningTreeIsoperimetry.HankelDegreeJump
