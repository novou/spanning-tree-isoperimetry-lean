import SpanningTreeIsoperimetry.CornerDeterminant

/-! Transposition and monotonicity in the sides of rectangular corner defects. -/
namespace SpanningTreeIsoperimetry.CornerEnergy
open Ferrers
open scoped BigOperators

def swapDirection : Fin 4 → Fin 4 := ![2,3,0,1]
def swapWord {ℓ : ℕ} (w : Word ℓ) : Word ℓ := fun i => swapDirection (w i)

theorem swapWord_involutive (ℓ : ℕ) : Function.Involutive (swapWord : Word ℓ → Word ℓ) := by
  intro w
  funext i
  change swapDirection (swapDirection (w i))=w i
  generalize w i=d
  fin_cases d <;> rfl

theorem position_swapWord {ℓ : ℕ} (w : Word ℓ) (t : ℕ) :
    position (swapWord w) t=(position w t).swap := by
  have hd (d : Fin 4) : direction (swapDirection d)=(direction d).swap := by
    fin_cases d <;> rfl
  apply Prod.ext <;>
    simp only [position,swapWord,Prod.fst_sum,Prod.snd_sum,Prod.fst_swap,Prod.snd_swap]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val<t <;> simp [hi,hd]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val<t <;> simp [hi,hd]

theorem visited_swapWord {ℓ : ℕ} (w : Word ℓ) : visited (swapWord w)=(visited w).image Prod.swap := by
  simp only [visited,Finset.image_image]
  apply Finset.image_congr
  intro i _
  exact position_swapWord w i

theorem normalizeVisited_swap (V : Finset Vertex) (hV : V.Nonempty) :
    normalizeVisited (V.image Prod.swap) (hV.image _) = transpose (normalizeVisited V hV) := by
  have hx : minimumX (V.image Prod.swap) (hV.image _)=minimumY V hV := by
    simp [minimumX,minimumY,Finset.image_image,Function.comp_def]
  have hy : minimumY (V.image Prod.swap) (hV.image _)=minimumX V hV := by
    simp [minimumX,minimumY,Finset.image_image,Function.comp_def]
  simp only [normalizeVisited,transpose,Finset.image_image]
  apply Finset.image_congr
  intro p _
  simp only [Function.comp_apply,normalizePoint,hx,hy,Prod.fst_swap,Prod.snd_swap]
  rfl

theorem normalizedVisited_swapWord {ℓ : ℕ} (w : Word ℓ) :
    normalizedVisited (swapWord w)=transpose (normalizedVisited w) := by
  simpa only [normalizedVisited,visited_swapWord] using
    normalizeVisited_swap (visited w) (visited_nonempty w)

def swapClosedWordEquiv (ℓ : ℕ) : ClosedWord ℓ ≃ ClosedWord ℓ where
  toFun w := ⟨swapWord w.val,by rw [position_swapWord,w.property]; rfl⟩
  invFun w := ⟨swapWord w.val,by rw [position_swapWord,w.property]; rfl⟩
  left_inv w := Subtype.ext (swapWord_involutive ℓ w.val)
  right_inv w := Subtype.ext (swapWord_involutive ℓ w.val)

theorem defectSum_transpose (M : Diagram) (ℓ : ℕ) : defectSum (transpose M) ℓ=defectSum M ℓ := by
  unfold defectSum
  rw [← (swapClosedWordEquiv ℓ).sum_comp]
  apply Finset.sum_congr rfl
  intro w _
  change defectCount (transpose M) (normalizedVisited (swapWord w.val))=_
  rw [normalizedVisited_swapWord,defectCount_transpose]

theorem realEnergy_transpose (M : Diagram) : realEnergy (transpose M)=realEnergy M := by
  rw [realEnergy_eq_tsum,realEnergy_eq_tsum]
  apply tsum_congr
  intro n
  simp only [realEnergyTerm,defectSum_transpose]

theorem faceRectangle_isFerrers (r s : ℕ) : IsFerrers (faceRectangle r s) := by
  intro p hp q hx hy
  rw [mem_faceRectangle] at hp ⊢
  omega

theorem duplicateRow_rectangle {r s : ℕ} (hs : 0<s) :
    duplicateRow (faceRectangle r s) 0=faceRectangle r (s+1) := by
  ext p
  rw [mem_duplicateRow_iff (faceRectangle_isFerrers r s),mem_faceRectangle]
  split_ifs <;> simp only [mem_faceRectangle,Prod.fst,Prod.snd] <;> omega

theorem rectangle_energy_succ {r s : ℕ} (hs : 0<s) :
    realEnergy (faceRectangle r s)≤realEnergy (faceRectangle r (s+1)) := by
  have h := realEnergy_duplicateRow (faceRectangle_isFerrers r s) 0
  rw [duplicateRow_rectangle hs] at h
  exact h

theorem rectangle_energy_mono_s {r s t : ℕ} (hs : 0<s) (hst : s≤t) :
    realEnergy (faceRectangle r s)≤realEnergy (faceRectangle r t) := by
  induction t,hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih => exact ih.trans (rectangle_energy_succ (by omega))

theorem rectangle_energy_mono {r s u v : ℕ} (hr : 0<r) (hs : 0<s) (hru : r≤u) (hsv : s≤v) :
    realEnergy (faceRectangle r s)≤realEnergy (faceRectangle u v) := by
  have h1 := rectangle_energy_mono_s (r := s) hr hru
  rw [← transpose_faceRectangle r s,← transpose_faceRectangle u s,realEnergy_transpose,
    realEnergy_transpose] at h1
  exact h1.trans (rectangle_energy_mono_s hs hsv)

end SpanningTreeIsoperimetry.CornerEnergy
