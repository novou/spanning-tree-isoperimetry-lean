import SpanningTreeIsoperimetry.FiniteShortDefectError
import SpanningTreeIsoperimetry.FiniteCornerOrientation

/-! Actual weighted finite corrections used by the small noncanonical
families. Arguments r,s are primal side lengths throughout. -/
namespace SpanningTreeIsoperimetry.SmallCornerCorrections
open Ferrers CornerEnergy CornerStripBridge FiniteGreenMonotonicity
open scoped Classical BigOperators
noncomputable section

def single (r s : ℕ) : ℝ := correction (faceRectangle (r-1) (s-1)) {(0,0)}
def strip (r s k : ℕ) : ℝ := correction (faceRectangle (r-1) (s-1)) (verticalDiagram k)
def square (r s : ℕ) : ℝ := correction (faceRectangle (r-1) (s-1)) (faceRectangle 2 2)

theorem single_antitone {r s R S : ℕ} (hr : r≤R) (hs : s≤S) : single R S≤single r s :=
  correction_antitone_ambient (rectangle_subset (by omega) (by omega))

theorem single_shift (r s i : ℕ) : single r s≤single r (s-i) := single_antitone le_rfl (by omega)

theorem single_lower {r s : ℕ} (hr : 2≤r) (hs : 2≤s) :
    5/(3*((min r s : ℕ) : ℝ)^4)<single r s :=
  (FiniteSingletonSquareLower.singleton_lower_primal hr hs).1

theorem single_square_lower {r : ℕ} (hr : 2≤r) : 12/(5*(r : ℝ)^4)<single r r :=
  (FiniteSingletonSquareLower.singleton_lower_primal hr hr).2

theorem single_ordered_lower {r s : ℕ} (hr : 2≤r) (hrs : r≤s) :
    5/(3*(r : ℝ)^4)<single r s := by
  simpa only [min_eq_left hrs] using single_lower hr (show 2≤s by omega)

theorem strip_two_lower {r s : ℕ} (hr : 5≤r) (hs : 3≤s) :
    21/(4*(r : ℝ)^4)<strip r s 2 := by
  have h := FiniteShortDefectError.two_cell_correction_lower (R := r-1) (S := s-1) (by omega) (by omega)
  have he : ((r-1 : ℕ) : ℝ)+1=(r : ℝ) := by exact_mod_cast (show r-1+1=r by omega)
  simpa only [he,strip] using h

theorem square_lower {r s : ℕ} (hr : 5≤r) (hs : 3≤s) : 20/(r : ℝ)^4<square r s := by
  have h := FiniteShortDefectError.square_defect_correction_lower (R := r-1) (S := s-1) (by omega) (by omega)
  have he : ((r-1 : ℕ) : ℝ)+1=(r : ℝ) := by exact_mod_cast (show r-1+1=r by omega)
  simpa only [he,square] using h

theorem strip_zero (r s : ℕ) : strip r s 0=0 := by simp [strip,verticalDiagram,correction_empty]
theorem strip_one (r s : ℕ) : strip r s 1=single r s := by
  have he : verticalDiagram 1=({(0,0)} : Diagram) := by decide +kernel
  rw [strip,he]
  rfl

theorem strip_ge_cells (r s k : ℕ) : (k : ℝ)*single r s≤strip r s k := by
  have h := correction_ge_card_mul_singleton (r-1) (s-1) (verticalDiagram k)
  simpa only [verticalDiagram,Finset.card_product,Finset.card_singleton,Finset.card_range,one_mul,single,strip] using h

theorem strip_transfer (r s : ℕ) {p q : ℕ} (hpq : p≤q) :
    strip r s p+(∑ i∈Finset.Ico p q, single r (s-i))≤strip r s q := by
  have hsub : verticalDiagram p⊆verticalDiagram q := by
    intro x hx
    have h := mem_verticalDiagram.mp hx
    exact mem_verticalDiagram.mpr ⟨h.1,by omega⟩
  have hd : verticalDiagram q\verticalDiagram p=({(0 : ℕ)} : Finset ℕ) ×ˢ Finset.Ico p q := by
    ext x
    simp only [Finset.mem_sdiff,mem_verticalDiagram,Finset.mem_product,Finset.mem_singleton,Finset.mem_Ico]
    omega
  have h := correction_transfer_rectangle (r-1) (s-1) hsub
  rw [hd,Finset.sum_product,Finset.sum_singleton] at h
  have he (i : ℕ) : s-1-i=s-i-1 := by omega
  simpa only [Prod.fst,Prod.snd,Nat.sub_zero,he,single,strip] using h

theorem strip_convex (r s k : ℕ) : 2*strip r s (k+1)≤strip r s k+strip r s (k+2) := by
  simpa only [strip,FiniteStripError.verticalDiagram_transpose] using
    correction_verticalStrip_convex (r-1) (s-1) k

theorem strip_four_ge_twice_two (r s : ℕ) : 2*strip r s 2≤strip r s 4 := by
  have h0 := strip_convex r s 0
  have h1 := strip_convex r s 1
  have h2 := strip_convex r s 2
  rw [strip_zero] at h0
  norm_num at h0 h1 h2
  linarith

/-- Any additional cells contribute at least the original singleton
correction, retaining the actual nonnegative finite-word transfer. -/
theorem transfer_card (r s : ℕ) {A B : Diagram} (hAB : A⊆B) :
    correction (faceRectangle (r-1) (s-1)) A+
      ((B.card-A.card : ℕ) : ℝ)*single r s≤correction (faceRectangle (r-1) (s-1)) B := by
  have hcell (p : Point) : single r s≤cellCorrection (faceRectangle (r-1) (s-1)) p := by
    have h := cellCorrection_mono_position (r-1) (s-1) (s := (0,0)) (t := p) (Nat.zero_le _) (Nat.zero_le _)
    simpa only [cellCorrection_rectangle,Nat.sub_zero,single] using h
  have hsum := Finset.sum_le_sum (s := B\A) (fun p _ => hcell p)
  rw [Finset.sum_const,nsmul_eq_mul,Finset.card_sdiff_of_subset hAB] at hsum
  have h := correction_transfer (U := faceRectangle (r-1) (s-1)) hAB
  linarith only [h,hsum]

theorem rectangle_six_lower {r s a b : ℕ} (hr : 5≤r) (hrs : r≤s)
    (hab : (a=2 ∧ b=3) ∨ (a=3 ∧ b=2)) :
    70/(3*(r : ℝ)^4)<correction (faceRectangle (r-1) (s-1)) (faceRectangle a b) := by
  have hsub : faceRectangle 2 2⊆faceRectangle a b := rectangle_subset (by rcases hab with h|h <;> omega)
    (by rcases hab with h|h <;> omega)
  have h := transfer_card r s hsub
  have hc : (faceRectangle a b).card-(faceRectangle 2 2).card=2 := by
    rcases hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num [faceRectangle]
  rw [hc] at h
  have hsquare := square_lower hr (by omega : 3≤s)
  have hsingle := single_ordered_lower (by omega : 2≤r) hrs
  change 20/(r : ℝ)^4<correction (faceRectangle (r-1) (s-1)) (faceRectangle 2 2) at hsquare
  norm_num at h
  have hid : 20/(r : ℝ)^4+2*(5/(3*(r : ℝ)^4))=70/(3*(r : ℝ)^4) := by ring
  linarith only [h,hsquare,hsingle,hid]

end
end SpanningTreeIsoperimetry.SmallCornerCorrections
