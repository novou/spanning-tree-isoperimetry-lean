import SpanningTreeIsoperimetry.BoundaryWalkCount
import SpanningTreeIsoperimetry.BoundaryHalfPlane
import SquareMaximality.ClosedWalk.Symmetry
import Mathlib.Data.Nat.Dist

/-! A second first-hit reflection gives actual quadrant boundary path counts.
The free horizontal coordinate may start at any nonnegative abscissa. -/
namespace SpanningTreeIsoperimetry.QuadrantWalkCount

open SquareMaximality.ClosedWalk BoundaryGreen
open scoped Classical

def NonnegativeY {n : ℕ} (w : Word n) : Prop := ∀ t≤n, 0≤(position w t).2

abbrev HalfPlaneAt (n : ℕ) (j : ℤ) :=
  {w : Word n // total w=(j,0) ∧ NonnegativeY w}

noncomputable instance (n : ℕ) (j : ℤ) : Fintype (HalfPlaneAt n j) := Fintype.ofFinite _

theorem position_reflect_snd {n σ t : ℕ} (w : Word n) :
    (position (reflectXAt σ w) t).2=(position w t).2 := by
  rw [position_snd_eq_sum,position_snd_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact stepAt_reflectXAt_snd w

theorem nonnegativeY_reflect {n σ : ℕ} (w : Word n) :
    NonnegativeY (reflectXAt σ w) ↔ NonnegativeY w := by
  simp only [NonnegativeY,position_reflect_snd]

def halfPlaneAtSwapEquiv (n j : ℕ) : HalfPlaneAt n j ≃ HalfPlaneWord n j where
  toFun w := ⟨swapWord w.val,by
    constructor
    · rw [total_swapWord,w.property.1]; rfl
    · intro x hx
      obtain ⟨t,ht,hx⟩ := mem_visitedX.mp hx
      rw [position_swapWord] at hx
      change (position w.val t).2=x at hx
      exact hx ▸ w.property.2 t ht⟩
  invFun w := ⟨swapWord w.val,by
    constructor
    · rw [total_swapWord,w.property.1]; rfl
    · intro t ht
      rw [position_swapWord]
      exact w.property.2 _ (mem_visitedX.mpr ⟨t,ht,rfl⟩)⟩
  left_inv w := Subtype.ext (swapWord_swapWord w.val)
  right_inv w := Subtype.ext (swapWord_swapWord w.val)

def halfPlaneAtNegEquiv (n : ℕ) (j : ℤ) : HalfPlaneAt n (-j) ≃ HalfPlaneAt n j where
  toFun w := ⟨reflectXAt 0 w.val,by
    constructor
    · apply Prod.ext
      · rw [← position_length,position_reflectXAt_zero_fst,position_length,w.property.1]; simp
      · rw [total_reflectXAt_snd,w.property.1]
    · exact (nonnegativeY_reflect w.val).mpr w.property.2⟩
  invFun w := ⟨reflectXAt 0 w.val,by
    constructor
    · apply Prod.ext
      · rw [← position_length,position_reflectXAt_zero_fst,position_length,w.property.1]
      · rw [total_reflectXAt_snd,w.property.1]
    · exact (nonnegativeY_reflect w.val).mpr w.property.2⟩
  left_inv w := by apply Subtype.ext; exact reflectXAt_involutive (σ := 0) w.val
  right_inv w := by apply Subtype.ext; exact reflectXAt_involutive (σ := 0) w.val

theorem halfPlaneAt_card_distance (n a b : ℕ) :
    Fintype.card (HalfPlaneAt n ((b : ℤ)-a))=
      Fintype.card (HalfPlaneWord n (Nat.dist a b)) := by
  by_cases hab : a≤b
  · rw [Nat.dist_eq_sub_of_le hab]
    have he : (b : ℤ)-a=((b-a : ℕ) : ℤ) := by omega
    rw [he]
    exact Fintype.card_congr (halfPlaneAtSwapEquiv n (b-a))
  · rw [Nat.dist_eq_sub_of_le_right (by omega : b≤a)]
    have he : (b : ℤ)-a=-((a-b : ℕ) : ℤ) := by omega
    rw [he,Fintype.card_congr (halfPlaneAtNegEquiv n ((a-b : ℕ) : ℤ))]
    exact Fintype.card_congr (halfPlaneAtSwapEquiv n (a-b))

def reflectAtLevel {n : ℕ} (w : Word n) (k : ℤ) (hk : k∈visitedX w) : Word n :=
  reflectXAt (firstHitX w k hk) w

theorem reflectAtLevel_total {n : ℕ} (w : Word n) (k : ℤ) (hk : k∈visitedX w) :
    total (reflectAtLevel w k hk)=(2*k-(total w).1,(total w).2) := by
  apply Prod.ext
  · rw [reflectAtLevel,total_reflectXAt_fst w (firstHitX_le_length w k hk),position_firstHitX]
  · exact total_reflectXAt_snd w

theorem reflectAtLevel_hits {n : ℕ} (w : Word n) (k : ℤ) (hk : k∈visitedX w) :
    k∈visitedX (reflectAtLevel w k hk) := by
  apply mem_visitedX.mpr
  refine ⟨firstHitX w k hk,firstHitX_le_length w k hk,?_⟩
  rw [reflectAtLevel,position_reflectXAt_of_le w le_rfl,position_firstHitX]

theorem reflectAtLevel_twice {n : ℕ} (w : Word n) (k : ℤ) (hk : k∈visitedX w)
    (hk' : k∈visitedX (reflectAtLevel w k hk)) :
    reflectAtLevel (reflectAtLevel w k hk) k hk'=w := by
  unfold reflectAtLevel
  rw [firstHitX_reflectXAt w k hk hk']
  exact reflectXAt_involutive w

theorem lower_iff_avoid {n : ℕ} (w : Word n) (a : ℕ) :
    (∀ x∈visitedX w, -(a : ℤ)≤x) ↔ (-(a : ℤ)-1)∉visitedX w := by
  constructor
  · intro h hx
    have := h _ hx
    omega
  · intro h x hx
    by_contra hn
    have hlo := Finset.min'_le _ _ hx
    have hhi := Finset.le_max' _ _ (zero_mem_visitedX w)
    exact h (between_min_max_mem_visitedX w (-(a : ℤ)-1) (by omega) (by omega))

theorem killing_level_visited {n a b : ℕ} (w : Word n)
    (hw : total w=(-(a : ℤ)-b-2,0)) : (-(a : ℤ)-1)∈visitedX w := by
  have he : (-(a : ℤ)-b-2)∈visitedX w :=
    mem_visitedX.mpr ⟨n,le_rfl,by rw [position_length,hw]⟩
  have hlo := Finset.min'_le _ _ he
  have hhi := Finset.le_max' _ _ (zero_mem_visitedX w)
  exact between_min_max_mem_visitedX w (-(a : ℤ)-1) (by omega) (by omega)

def badQuadrantEquiv (n a b : ℕ) :
    {w : Word n // total w=((b : ℤ)-a,0) ∧ NonnegativeY w ∧ (-(a : ℤ)-1)∈visitedX w} ≃
      HalfPlaneAt n (-(a : ℤ)-b-2) where
  toFun w := ⟨reflectAtLevel w.val (-(a : ℤ)-1) w.property.2.2,by
    constructor
    · rw [reflectAtLevel_total,w.property.1]; congr 1 <;> ring
    · exact (nonnegativeY_reflect w.val).mpr w.property.2.1⟩
  invFun w := ⟨reflectAtLevel w.val (-(a : ℤ)-1) (killing_level_visited w.val w.property.1),by
    constructor
    · rw [reflectAtLevel_total,w.property.1]; congr 1 <;> ring
    · exact ⟨(nonnegativeY_reflect w.val).mpr w.property.2,
        reflectAtLevel_hits _ _ _⟩⟩
  left_inv w := Subtype.ext (reflectAtLevel_twice _ _ _ _)
  right_inv w := Subtype.ext (reflectAtLevel_twice _ _ _ _)

abbrev QuadrantBoundaryWord (n a b : ℕ) :=
  {w : Word n // total w=((b : ℤ)-a,0) ∧ NonnegativeY w ∧ ∀ x∈visitedX w, -(a : ℤ)≤x}

noncomputable instance (n a b : ℕ) : Fintype (QuadrantBoundaryWord n a b) := Fintype.ofFinite _

/-- The image term is the half-plane path count at displacement a+b+2. -/
theorem quadrant_count_partition (n a b : ℕ) :
    Fintype.card (QuadrantBoundaryWord n a b)+Fintype.card (HalfPlaneWord n (a+b+2))=
      Fintype.card (HalfPlaneWord n (Nat.dist a b)) := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Word n)).filter
      (fun w => total w=((b : ℤ)-a,0) ∧ NonnegativeY w))
    (fun w => (-(a : ℤ)-1)∈visitedX w)
  simp only [Finset.filter_filter] at h
  rw [← Fintype.card_subtype,← Fintype.card_subtype,← Fintype.card_subtype] at h
  have hb : Fintype.card {w : Word n //
      (total w=((b : ℤ)-a,0) ∧ NonnegativeY w) ∧ (-(a : ℤ)-1)∈visitedX w}=
      Fintype.card (HalfPlaneWord n (a+b+2)) := by
    let e1 : {w : Word n // (total w=((b : ℤ)-a,0) ∧ NonnegativeY w) ∧
        (-(a : ℤ)-1)∈visitedX w} ≃
        {w : Word n // total w=((b : ℤ)-a,0) ∧ NonnegativeY w ∧
        (-(a : ℤ)-1)∈visitedX w} :=
      (Equiv.refl (Word n)).subtypeEquiv (fun _ => and_assoc)
    have he : -(a : ℤ)-b-2=-((a+b+2 : ℕ) : ℤ) := by push_cast; ring
    calc
      _=Fintype.card (HalfPlaneAt n (-(a : ℤ)-b-2)) := Fintype.card_congr
        (e1.trans (badQuadrantEquiv n a b))
      _=Fintype.card (HalfPlaneAt n ((a+b+2 : ℕ) : ℤ)) := by
        rw [he]; exact Fintype.card_congr (halfPlaneAtNegEquiv n _)
      _=_ := Fintype.card_congr (halfPlaneAtSwapEquiv n (a+b+2))
  have hg : Fintype.card {w : Word n //
      (total w=((b : ℤ)-a,0) ∧ NonnegativeY w) ∧ (-(a : ℤ)-1)∉visitedX w}=
      Fintype.card (QuadrantBoundaryWord n a b) := by
    apply Fintype.card_congr
    exact (Equiv.refl (Word n)).subtypeEquiv (fun w =>
      and_assoc.trans (and_congr Iff.rfl (and_congr Iff.rfl (lower_iff_avoid w a).symm)))
  rw [hb,hg,halfPlaneAt_card_distance] at h
  omega

noncomputable def quadrantCoefficient (n a b : ℕ) : ℝ :=
  (Fintype.card (QuadrantBoundaryWord n a b) : ℝ)/(4 : ℝ)^(n+1)

theorem quadrantCoefficient_eq (n a b : ℕ) :
    quadrantCoefficient n a b=halfPlaneCoefficient n (Nat.dist a b)-
      halfPlaneCoefficient n (a+b+2) := by
  have h : (Fintype.card (QuadrantBoundaryWord n a b) : ℝ)+
      Fintype.card (HalfPlaneWord n (a+b+2))=Fintype.card (HalfPlaneWord n (Nat.dist a b)) :=
    by exact_mod_cast quadrant_count_partition n a b
  unfold quadrantCoefficient halfPlaneCoefficient
  rw [← sub_div]
  congr 1
  linarith

theorem quadrantCoefficient_nonneg (n a b : ℕ) : 0≤quadrantCoefficient n a b := by
  unfold quadrantCoefficient
  positivity

theorem quadrantCoefficient_le_halfPlane (n a b : ℕ) :
    quadrantCoefficient n a b≤halfPlaneCoefficient n (Nat.dist a b) := by
  rw [quadrantCoefficient_eq]
  exact sub_le_self _ (halfPlaneCoefficient_nonneg _ _)

/-- All currently evaluated quadrant boundary entries are exact differences
of the already summed half-plane series. -/
theorem quadrantCoefficient_hasSum {a b : ℕ} (h : a+b+2<6) :
    HasSum (fun n => quadrantCoefficient n a b)
      (boundaryValue ⟨Nat.dist a b,by unfold Nat.dist; omega⟩-
        boundaryValue ⟨a+b+2,h⟩) := by
  have hdist : Nat.dist a b<6 := by unfold Nat.dist; omega
  simpa only [quadrantCoefficient_eq] using
    (halfPlaneCoefficient_hasSum ⟨Nat.dist a b,hdist⟩).sub
      (halfPlaneCoefficient_hasSum ⟨a+b+2,h⟩)

end SpanningTreeIsoperimetry.QuadrantWalkCount
