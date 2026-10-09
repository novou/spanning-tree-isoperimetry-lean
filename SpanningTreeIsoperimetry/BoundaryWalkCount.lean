import SpanningTreeIsoperimetry.HalfPlaneWords
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import SquareMaximality.ClosedWalk.PlaneFirstHit

namespace SpanningTreeIsoperimetry.BoundaryGreen
open SquareMaximality.ClosedWalk
open scoped BigOperators

/-- Unrestricted endpoint counts in two-sign coordinates. -/
theorem total_eq_iff_sign_card (n r s : ℕ) (w : Word n) :
    total w = ((r : ℤ) + s - n, (r : ℤ) - s) ↔
      (firstSignSet w).card = r ∧ (secondSignSet w).card = s := by
  have h1 := first_sign_sum_card w
  have h2 := second_sign_sum_card w
  rw [first_sign_sum_eq] at h1
  rw [second_sign_sum_eq] at h2
  rw [Prod.ext_iff]
  dsimp only
  omega

def endpointSignEquiv (n r s : ℕ) :
    {w : Word n // total w = ((r : ℤ) + s - n, (r : ℤ) - s)} ≃
      {a : Finset (Fin n) // a.card = r} × {b : Finset (Fin n) // b.card = s} :=
  ((wordEquivSignSets n).subtypeEquiv (fun w => total_eq_iff_sign_card n r s w)).trans
    Equiv.subtypeProdEquivProd

theorem endpoint_count (n r s : ℕ) :
    Fintype.card {w : Word n // total w = ((r : ℤ) + s - n, (r : ℤ) - s)} =
      n.choose r * n.choose s := by
  rw [Fintype.card_congr (endpointSignEquiv n r s), Fintype.card_prod]
  simp only [Fintype.card_finset_len, Fintype.card_fin]

/-- An endpoint to the left of the killing line necessarily crosses that line. -/
theorem minus_one_visited_of_endpoint {n : ℕ} (w : Word n) (hy : ℤ)
    (hw : total w = (-2, hy)) : -1 ∈ visitedX w := by
  have hm : (-2 : ℤ) ∈ visitedX w := by
    apply mem_visitedX.mpr
    exact ⟨n, le_rfl, by rw [position_length, hw]⟩
  apply between_min_max_mem_visitedX
  · exact (Finset.min'_le _ _ hm).trans (by norm_num)
  · exact (show (-1 : ℤ) ≤ 0 by norm_num).trans
      (Finset.le_max' _ _ (zero_mem_visitedX w))

def reflectedAtMinusOne {n : ℕ} (w : Word n) (hw : -1 ∈ visitedX w) : Word n :=
  reflectXAt (firstHitX w (-1) hw) w

theorem reflectedAtMinusOne_fst {n : ℕ} (w : Word n) (hw : -1 ∈ visitedX w) :
    (total (reflectedAtMinusOne w hw)).1 = -2 - (total w).1 := by
  rw [reflectedAtMinusOne, total_reflectXAt_fst w (firstHitX_le_length w (-1) hw),
    position_firstHitX]
  ring

theorem reflectedAtMinusOne_snd {n : ℕ} (w : Word n) (hw : -1 ∈ visitedX w) :
    (total (reflectedAtMinusOne w hw)).2 = (total w).2 := total_reflectXAt_snd w

theorem reflectedAtMinusOne_hits {n : ℕ} (w : Word n) (hw : -1 ∈ visitedX w) :
    -1 ∈ visitedX (reflectedAtMinusOne w hw) := by
  apply mem_visitedX.mpr
  refine ⟨firstHitX w (-1) hw, firstHitX_le_length w (-1) hw, ?_⟩
  rw [reflectedAtMinusOne, position_reflectXAt_of_le w le_rfl, position_firstHitX]

theorem reflectedAtMinusOne_twice {n : ℕ} (w : Word n) (hw : -1 ∈ visitedX w)
    (hwr : -1 ∈ visitedX (reflectedAtMinusOne w hw)) :
    reflectedAtMinusOne (reflectedAtMinusOne w hw) hwr = w := by
  unfold reflectedAtMinusOne
  rw [firstHitX_reflectXAt w (-1) hw hwr]
  exact reflectXAt_involutive w

def badBoundaryEquiv (n : ℕ) (j : ℤ) :
    {w : Word n // total w = (0,j) ∧ -1 ∈ visitedX w} ≃
      {w : Word n // total w = (-2,j)} where
  toFun w := ⟨reflectedAtMinusOne w.val w.property.2, by
    apply Prod.ext
    · rw [reflectedAtMinusOne_fst, w.property.1]; rfl
    · rw [reflectedAtMinusOne_snd, w.property.1]⟩
  invFun w := ⟨reflectedAtMinusOne w.val (minus_one_visited_of_endpoint w.val j w.property), by
    constructor
    · apply Prod.ext
      · rw [reflectedAtMinusOne_fst, w.property]; norm_num
      · rw [reflectedAtMinusOne_snd, w.property]
    · exact reflectedAtMinusOne_hits _ _⟩
  left_inv w := Subtype.ext (reflectedAtMinusOne_twice _ _ _)
  right_inv w := Subtype.ext (reflectedAtMinusOne_twice _ _ _)

/-- Staying on the nonnegative side is exactly avoiding the first killing line. -/
theorem nonnegative_iff_avoid_minus_one {n : ℕ} (w : Word n) :
    (∀ x ∈ visitedX w, 0 ≤ x) ↔ (-1 : ℤ) ∉ visitedX w := by
  constructor
  · intro h hm
    have := h (-1) hm
    omega
  · intro h x hx
    by_contra hn
    have hlo : (visitedX w).min' (visitedX_nonempty w) ≤ -1 := by
      have := Finset.min'_le _ _ hx
      omega
    have hhi : (-1 : ℤ) ≤ (visitedX w).max' (visitedX_nonempty w) := by
      have := Finset.le_max' _ _ (zero_mem_visitedX w)
      omega
    exact h (between_min_max_mem_visitedX w (-1) hlo hhi)

theorem halfPlane_count_partition (n j : ℕ) :
    Fintype.card (HalfPlaneWord n j) +
      Fintype.card {w : Word n // total w = (-2,(j : ℤ))} =
      Fintype.card {w : Word n // total w = (0,(j : ℤ))} := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Word n)).filter (fun w => total w = (0,(j : ℤ))))
    (fun w => (-1 : ℤ) ∈ visitedX w)
  simp only [Finset.filter_filter] at h
  rw [← Fintype.card_subtype, ← Fintype.card_subtype, ← Fintype.card_subtype] at h
  have hg : Fintype.card (HalfPlaneWord n j) =
      Fintype.card {w : Word n // total w = (0,(j : ℤ)) ∧ (-1 : ℤ) ∉ visitedX w} := by
    apply Fintype.card_congr
    exact (Equiv.refl (Word n)).subtypeEquiv
      (fun w => and_congr Iff.rfl (nonnegative_iff_avoid_minus_one w))
  rw [Fintype.card_congr (badBoundaryEquiv n (j : ℤ))] at h
  omega

theorem halfPlane_count_wrongParity (m j : ℕ) :
    Fintype.card (HalfPlaneWord (2*m+1+j) j) = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun w => ?_⟩
  have h := first_sign_sum_card w.val
  rw [first_sign_sum_eq, w.property.1] at h
  dsimp only at h
  omega

theorem halfPlane_count_short {n j : ℕ} (h : n < j) :
    Fintype.card (HalfPlaneWord n j) = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun w => ?_⟩
  have ht := second_sign_sum_card w.val
  rw [second_sign_sum_eq, w.property.1] at ht
  dsimp only at ht
  omega

theorem unrestricted_boundary_count (m j : ℕ) :
    Fintype.card {w : Word (2*m+j) // total w = (0,(j : ℤ))} =
      (Nat.choose (2*m+j) m)^2 := by
  have h := endpoint_count (2*m+j) (m+j) m
  have he : (((m+j : ℕ) : ℤ)+(m : ℤ)-(2*m+j : ℕ), ((m+j : ℕ) : ℤ)-(m : ℤ)) =
      (0,(j : ℤ)) := by ext <;> push_cast <;> ring
  rw [he, Nat.choose_symm_of_eq_add (show 2*m+j = (m+j)+m by omega)] at h
  simpa only [pow_two] using h

theorem reflected_boundary_count (m j : ℕ) (hm : 0 < m) :
    Fintype.card {w : Word (2*m+j) // total w = (-2,(j : ℤ))} =
      Nat.choose (2*m+j) (m+1) * Nat.choose (2*m+j) (m-1) := by
  have h := endpoint_count (2*m+j) (m+j-1) (m-1)
  have he : (((m+j-1 : ℕ) : ℤ)+((m-1 : ℕ) : ℤ)-(2*m+j : ℕ),
      ((m+j-1 : ℕ) : ℤ)-((m-1 : ℕ) : ℤ)) = (-2,(j : ℤ)) := by
    ext <;> omega
  rw [he, Nat.choose_symm_of_eq_add (show 2*m+j = (m+j-1)+(m+1) by omega)] at h
  exact h

theorem reflected_boundary_count_zero (j : ℕ) :
    Fintype.card {w : Word j // total w = (-2,(j : ℤ))} = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun w => ?_⟩
  have ht := second_sign_sum_card w.val
  rw [second_sign_sum_eq, w.property] at ht
  dsimp only at ht
  omega

theorem halfPlane_count_real (m j : ℕ) :
    (Fintype.card (HalfPlaneWord (2*m+j) j) : ℝ) =
      (Nat.choose (2*m+j) m : ℝ)^2 * (2*m+j+1) /
        ((m+1)*(m+j+1)) := by
  by_cases hm : m = 0
  · subst m
    have hp := halfPlane_count_partition j j
    rw [reflected_boundary_count_zero] at hp
    have ha : Fintype.card {w : Word j // total w=(0,(j : ℤ))}=1 := by
      simpa only [Nat.cast_zero,add_zero,sub_self,sub_zero,Nat.choose_self,
        Nat.choose_zero_right,mul_one] using endpoint_count j j 0
    rw [ha] at hp
    norm_num at hp
    norm_num [hp,show (j : ℝ)+1≠0 by positivity]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hc := halfPlane_count_partition (2*m+j) j
  rw [unrestricted_boundary_count, reflected_boundary_count m j hmpos] at hc
  have hcR : (Fintype.card (HalfPlaneWord (2*m+j) j) : ℝ) +
      (Nat.choose (2*m+j) (m+1) : ℝ) * Nat.choose (2*m+j) (m-1) =
      (Nat.choose (2*m+j) m : ℝ)^2 := by exact_mod_cast hc
  have ha := Nat.choose_succ_right_eq (2*m+j) m
  have hb := Nat.choose_succ_right_eq (2*m+j) (m-1)
  rw [show 2*m+j-m = m+j by omega] at ha
  rw [show m-1+1=m by omega, show 2*m+j-(m-1)=m+j+1 by omega] at hb
  have haR : (Nat.choose (2*m+j) (m+1) : ℝ) * (m+1) =
      (Nat.choose (2*m+j) m : ℝ) * (m+j) := by exact_mod_cast ha
  have hbR : (Nat.choose (2*m+j) m : ℝ) * m =
      (Nat.choose (2*m+j) (m-1) : ℝ) * (m+j+1) := by exact_mod_cast hb
  have hp : (Nat.choose (2*m+j) (m+1) : ℝ) * Nat.choose (2*m+j) (m-1) *
      ((m+1)*(m+j+1)) = (Nat.choose (2*m+j) m : ℝ)^2 * (m*(m+j)) := by
    calc
      _ = ((Nat.choose (2*m+j) (m+1) : ℝ) * (m+1)) *
          ((Nat.choose (2*m+j) (m-1) : ℝ) * (m+j+1)) := by ring
      _ = ((Nat.choose (2*m+j) m : ℝ) * (m+j)) *
          ((Nat.choose (2*m+j) m : ℝ) * m) := by rw [haR, ← hbR]
      _ = _ := by ring
  rw [eq_div_iff (by positivity : ((m : ℝ)+1)*(m+j+1) ≠ 0)]
  have he := congrArg (fun x : ℝ => x * (((m : ℝ)+1)*(m+j+1))) hcR
  nlinarith only [he, hp]

end SpanningTreeIsoperimetry.BoundaryGreen
