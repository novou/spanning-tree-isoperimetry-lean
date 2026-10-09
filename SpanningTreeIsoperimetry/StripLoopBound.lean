import SpanningTreeIsoperimetry.CornerDeterminant
import SpanningTreeIsoperimetry.DeterminantComparison

/-!
# Finite loop comparisons for the uniform strip-energy bound

The finite statements isolate the bottom-row diameter removed by horizontal
reflection and bound translations meeting both sides of a boundary cut.
The later Green-minor comparison uses only these actual placement counts.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SpanningTreeIsoperimetry.StripLoopBound

open Ferrers CornerEnergy
open scoped BigOperators

noncomputable section

/-- Rightmost visited abscissa on the lowest row of a normalized pattern. -/
def lastAxisX (P : Diagram) : ℕ := (axisAbscissae P).sup id

def bottomWidth (P : Diagram) (hP : IsNormalized P) : ℕ := lastAxisX P - firstAxisX P hP

private theorem axis_mem_iff {P : Diagram} {x : ℕ} : x ∈ axisAbscissae P ↔ (x,0) ∈ P := by
  constructor
  · intro hx
    obtain ⟨p,hp,hpx⟩ := Finset.mem_image.mp hx
    obtain ⟨hpP,hp0⟩ := Finset.mem_filter.mp hp
    have he : p = (x,0) := Prod.ext hpx hp0
    simpa only [he] using hpP
  · intro hx
    exact Finset.mem_image.mpr ⟨(x,0),Finset.mem_filter.mpr ⟨hx,rfl⟩,rfl⟩

theorem lastAxisX_mem {P : Diagram} (hP : IsNormalized P) : (lastAxisX P,0) ∈ P := by
  obtain ⟨x,hx,he⟩ := Finset.exists_mem_eq_sup (axisAbscissae P) (axisAbscissae_nonempty hP) id
  apply axis_mem_iff.mp
  simpa only [lastAxisX,he,id_eq] using hx

theorem axis_le_last {P : Diagram} {p : Point} (hp : p ∈ P) (hp0 : p.2 = 0) :
    p.1 ≤ lastAxisX P := by
  apply Finset.le_sup (f := id)
  apply axis_mem_iff.mpr
  simpa only [← hp0,Prod.mk.eta] using hp

theorem firstAxis_le_last {P : Diagram} (hP : IsNormalized P) :
    firstAxisX P hP ≤ lastAxisX P := firstAxisX_le hP (lastAxisX_mem hP) rfl

theorem lastAxis_le_span {P : Diagram} (hP : IsNormalized P) :
    lastAxisX P ≤ P.sup Prod.fst := Finset.le_sup (f := Prod.fst) (lastAxisX_mem hP)

/-- Horizontal reflection in the bounding box of a normalized pattern. -/
def mirrorPattern (P : Diagram) : Diagram := P.image (fun p => (P.sup Prod.fst-p.1,p.2))

theorem mirrorPattern_normalized {P : Diagram} (hP : IsNormalized P) :
    IsNormalized (mirrorPattern P) := by
  have hn : P.Nonempty := by obtain ⟨p,hp,_⟩ := hP.1; exact ⟨p,hp⟩
  obtain ⟨p,hp,hmax⟩ := Finset.exists_mem_eq_sup P hn Prod.fst
  constructor
  · refine ⟨(P.sup Prod.fst-p.1,p.2),Finset.mem_image.mpr ⟨p,hp,rfl⟩,?_⟩
    simp [hmax]
  · refine ⟨(P.sup Prod.fst-firstAxisX P hP,0),?_,rfl⟩
    exact Finset.mem_image.mpr ⟨(firstAxisX P hP,0),firstAxisX_mem hP,rfl⟩

theorem firstAxis_mirror {P : Diagram} (hP : IsNormalized P) :
    firstAxisX (mirrorPattern P) (mirrorPattern_normalized hP) =
      P.sup Prod.fst-lastAxisX P := by
  apply le_antisymm
  · apply firstAxisX_le (mirrorPattern_normalized hP)
      (Finset.mem_image.mpr ⟨(lastAxisX P,0),lastAxisX_mem hP,rfl⟩) rfl
  · have hm := firstAxisX_mem (mirrorPattern_normalized hP)
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hm
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    have hp0 : p.2 = 0 := hy
    have hl := axis_le_last hp hp0
    dsimp at hx
    omega

/-- Reflection removes exactly the width of the visits on the lowest row. -/
theorem firstAxis_reflection_identity {P : Diagram} (hP : IsNormalized P) :
    firstAxisX P hP + firstAxisX (mirrorPattern P) (mirrorPattern_normalized hP) +
      bottomWidth P hP = P.sup Prod.fst := by
  rw [firstAxis_mirror hP]
  unfold bottomWidth
  have hfirst := firstAxis_le_last hP
  have hlast := lastAxis_le_span hP
  omega

/-- Translations fitting the ambient set and hitting both prescribed sets.
The ambient anchor is retained separately; no Ferrers assumption is imposed
on the two marked sets. -/
def hitBothStarts (U A B P : Diagram) : Diagram := by
  classical
  exact (fittingStarts U P).filter (fun t =>
    (∃ p ∈ P, shift t p ∈ A) ∧ (∃ p ∈ P, shift t p ∈ B))

private theorem hitBoth_bounds {U A B P : Diagram} (hP : IsNormalized P) (cut : ℕ)
    (hA : ∀ p ∈ A, p.2 = 0 ∧ p.1 < cut)
    (hB : ∀ p ∈ B, p.2 = 0 ∧ cut ≤ p.1)
    {t : Point} (ht : t ∈ hitBothStarts U A B P) :
    t.2 = 0 ∧ cut-lastAxisX P ≤ t.1 ∧ t.1 < cut-firstAxisX P hP := by
  obtain ⟨_,⟨p,hp,hpa⟩,⟨q,hq,hqb⟩⟩ := Finset.mem_filter.mp ht
  have ha := hA _ hpa
  have hb := hB _ hqb
  have hp0 : p.2 = 0 := by dsimp [shift] at ha; omega
  have hq0 : q.2 = 0 := by dsimp [shift] at hb; omega
  have hmin := firstAxisX_le hP hp hp0
  have hmax := axis_le_last hq hq0
  dsimp [shift] at ha hb
  omega

/-- A loop pattern has at most its bottom-row diameter many horizontal
translations meeting both sides of one boundary cut. -/
theorem card_hitBoth_le_bottomWidth {U A B P : Diagram} (hP : IsNormalized P) (cut : ℕ)
    (hA : ∀ p ∈ A, p.2 = 0 ∧ p.1 < cut)
    (hB : ∀ p ∈ B, p.2 = 0 ∧ cut ≤ p.1) :
    (hitBothStarts U A B P).card ≤ bottomWidth P hP := by
  have hcard : (hitBothStarts U A B P).card ≤
      (Finset.Ico (cut-lastAxisX P) (cut-firstAxisX P hP)).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro t ht
      have hb := hitBoth_bounds hP cut hA hB ht
      exact Finset.mem_Ico.mpr ⟨hb.2.1,hb.2.2⟩
    · intro t ht u hu he
      have ht0 := (hitBoth_bounds hP cut hA hB ht).1
      have hu0 := (hitBoth_bounds hP cut hA hB hu).1
      exact Prod.ext he (ht0.trans hu0.symm)
  have hfirst := firstAxis_le_last hP
  simp only [Nat.card_Ico] at hcard
  unfold bottomWidth
  omega

open SquareMaximality.Boundary.DeterminantSeries

/-- Inclusion–exclusion of actual finite adjacency traces. The combinatorial
interpretation counts loops visiting both marked sets. -/
def hitBothTraceTerm (U A B : Diagram) (i : ℕ) : ℝ :=
  faceTraceTerm U i - faceTraceTerm (U \ A) i - faceTraceTerm (U \ B) i +
    faceTraceTerm (U \ (A ∪ B)) i

/-- The finite loop-correlation series is the logarithm of three actual
Green minors. This holds for arbitrary disjoint marked sets, with no Ferrers
condition and no determinant-limit theorem. -/
theorem hitBothTraceTerm_hasSum {m n : ℕ} {U A B : Diagram}
    (hU : U ⊆ faceRectangle m n) (hA : A ⊆ U) (hB : B ⊆ U) (hd : Disjoint A B) :
    HasSum (hitBothTraceTerm U A B)
      (Real.log (Matrix.det (greenMinor hA)) + Real.log (Matrix.det (greenMinor hB)) -
        Real.log (Matrix.det (greenMinor (Finset.union_subset hA hB)))) := by
  have hspec {V : Diagram} (hV : V ⊆ U) : FaceAdjacencySpectralBound V := by
    apply SquareMaximality.Boundary.SpectralBound.faceAdjacencySpectralBound_of_subset
    simpa only [foundation_faceIndices] using hV.trans hU
  have hu := hasSum_faceTraceTerm U (hspec (Finset.Subset.refl _))
  have hua := hasSum_faceTraceTerm (U \ A) (hspec Finset.sdiff_subset)
  have hub := hasSum_faceTraceTerm (U \ B) (hspec Finset.sdiff_subset)
  have huab := hasSum_faceTraceTerm (U \ (A ∪ B)) (hspec Finset.sdiff_subset)
  have hseries := ((hu.sub hua).sub hub).add huab
  have hlog {M : Diagram} (hM : M ⊆ U) :
      Real.log (Matrix.det (SquareMaximality.Boundary.fourIminusAdjacency (U \ M))) =
        Real.log (Matrix.det (SquareMaximality.Boundary.fourIminusAdjacency U)) +
          Real.log (Matrix.det (greenMinor hM)) := by
    rw [greenMinor_det_identity hU hM,
      Real.log_mul (dirichlet_posDef hU).det_pos.ne' (greenMinor_det_pos hU hM).ne']
  have hAcard : (U \ A).card + A.card = U.card := by
    rw [Finset.card_sdiff_of_subset hA, Nat.sub_add_cancel (Finset.card_le_card hA)]
  have hBcard : (U \ B).card + B.card = U.card := by
    rw [Finset.card_sdiff_of_subset hB, Nat.sub_add_cancel (Finset.card_le_card hB)]
  have hABcard : (U \ (A ∪ B)).card + (A.card+B.card) = U.card := by
    rw [← Finset.card_union_of_disjoint hd, Finset.card_sdiff_of_subset (Finset.union_subset hA hB),
      Nat.sub_add_cancel (Finset.card_le_card (Finset.union_subset hA hB))]
  have haR : ((U \ A).card : ℝ) + A.card = U.card := by exact_mod_cast hAcard
  have hbR : ((U \ B).card : ℝ) + B.card = U.card := by exact_mod_cast hBcard
  have habR : ((U \ (A ∪ B)).card : ℝ) + (A.card+B.card) = U.card := by exact_mod_cast hABcard
  have hc : ((U.card : ℝ) - (U \ A).card - (U \ B).card + (U \ (A ∪ B)).card) *
      Real.log 4 = 0 := by
    have : (U.card : ℝ) - (U \ A).card - (U \ B).card + (U \ (A ∪ B)).card = 0 := by linarith
    rw [this,zero_mul]
  rw [hlog hA,hlog hB,hlog (Finset.union_subset hA hB)] at hseries
  convert hseries using 1
  · rfl
  · nlinarith

private def reflectVertex (p : Vertex) : Vertex := (-p.1,p.2)

def reflectDirection : Fin 4 → Fin 4 := ![1,0,2,3]

def reflectWord {ℓ : ℕ} (w : Word ℓ) : Word ℓ := fun i => reflectDirection (w i)

private theorem reflectVertex_sum {I : Type*} (s : Finset I) (f : I → Vertex) :
    reflectVertex (∑ i ∈ s, f i) = ∑ i ∈ s, reflectVertex (f i) := by
  apply Prod.ext <;> simp [reflectVertex,Prod.fst_sum,Prod.snd_sum,Finset.sum_neg_distrib]

private theorem reflectDirection_vector (d : Fin 4) :
    direction (reflectDirection d) = reflectVertex (direction d) := by
  fin_cases d <;> rfl

theorem position_reflectWord {ℓ : ℕ} (w : Word ℓ) (t : ℕ) :
    position (reflectWord w) t = reflectVertex (position w t) := by
  unfold position reflectWord
  rw [reflectVertex_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < t <;> simp [hi,reflectDirection_vector,reflectVertex] <;> rfl

theorem reflectWord_involutive (ℓ : ℕ) : Function.Involutive (reflectWord : Word ℓ → Word ℓ) := by
  intro w
  funext i
  change reflectDirection (reflectDirection (w i)) = w i
  generalize w i = d
  fin_cases d <;> rfl

theorem visited_reflectWord {ℓ : ℕ} (w : Word ℓ) :
    visited (reflectWord w) = (visited w).image reflectVertex := by
  simp only [visited,Finset.image_image]
  apply Finset.image_congr
  intro i _
  exact position_reflectWord w i

private def maximumX (V : Finset Vertex) (hV : V.Nonempty) : ℤ :=
  (V.image Prod.fst).max' (hV.image _)

private theorem maximumX_mem (V : Finset Vertex) (hV : V.Nonempty) :
    ∃ p ∈ V, p.1 = maximumX V hV := by
  exact Finset.mem_image.mp (Finset.max'_mem (V.image Prod.fst) (hV.image _))

private theorem le_maximumX {V : Finset Vertex} (hV : V.Nonempty) {p : Vertex} (hp : p ∈ V) :
    p.1 ≤ maximumX V hV := Finset.le_max' _ _ (Finset.mem_image_of_mem _ hp)

private theorem minimumX_reflect (V : Finset Vertex) (hV : V.Nonempty) :
    minimumX (V.image reflectVertex) (hV.image _) = -maximumX V hV := by
  apply le_antisymm
  · obtain ⟨p,hp,hx⟩ := maximumX_mem V hV
    have h := minimumX_le (hV.image reflectVertex) (Finset.mem_image_of_mem reflectVertex hp)
    change minimumX (V.image reflectVertex) (hV.image _) ≤ -p.1 at h
    simpa only [hx] using h
  · apply Finset.le_min'
    intro x hx
    obtain ⟨q,hq,hqx⟩ := Finset.mem_image.mp hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    have hmax := le_maximumX hV hp
    dsimp [reflectVertex] at hqx
    omega

private theorem minimumY_reflect (V : Finset Vertex) (hV : V.Nonempty) :
    minimumY (V.image reflectVertex) (hV.image _) = minimumY V hV := by
  simp [minimumY,Finset.image_image,reflectVertex,Function.comp_def]

private theorem normalized_sup (V : Finset Vertex) (hV : V.Nonempty) :
    (normalizeVisited V hV).sup Prod.fst = (maximumX V hV-minimumX V hV).toNat := by
  apply le_antisymm
  · apply Finset.sup_le
    intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    have hm := minimumX_le hV hp
    have hx := le_maximumX hV hp
    have hc := (normalizePoint_cast hV hp).1
    omega
  · obtain ⟨p,hp,hx⟩ := maximumX_mem V hV
    have h := Finset.le_sup (f := Prod.fst) (Finset.mem_image_of_mem (normalizePoint V hV) hp)
    simpa only [normalizePoint,hx,normalizeVisited] using h

private theorem normalizePoint_reflect (V : Finset Vertex) (hV : V.Nonempty)
    {p : Vertex} (hp : p ∈ V) :
    normalizePoint (V.image reflectVertex) (hV.image _) (reflectVertex p) =
      ((normalizeVisited V hV).sup Prod.fst-(normalizePoint V hV p).1,
        (normalizePoint V hV p).2) := by
  have hlo := minimumX_le hV hp
  have hhi := le_maximumX hV hp
  apply Prod.ext
  · change (-p.1-minimumX (V.image reflectVertex) (hV.image _)).toNat =
      (normalizeVisited V hV).sup Prod.fst-(p.1-minimumX V hV).toNat
    rw [minimumX_reflect V hV,normalized_sup V hV]
    omega
  · change (p.2-minimumY (V.image reflectVertex) (hV.image _)).toNat =
      (p.2-minimumY V hV).toNat
    rw [minimumY_reflect V hV]

theorem normalizeVisited_reflect (V : Finset Vertex) (hV : V.Nonempty) :
    normalizeVisited (V.image reflectVertex) (hV.image _) = mirrorPattern (normalizeVisited V hV) := by
  change (V.image reflectVertex).image (normalizePoint (V.image reflectVertex) (hV.image _)) =
    (V.image (normalizePoint V hV)).image
      (fun p => ((normalizeVisited V hV).sup Prod.fst-p.1,p.2))
  rw [Finset.image_image,Finset.image_image]
  apply Finset.image_congr
  intro p hp
  exact normalizePoint_reflect V hV hp

theorem normalizedVisited_reflectWord {ℓ : ℕ} (w : Word ℓ) :
    normalizedVisited (reflectWord w) = mirrorPattern (normalizedVisited w) := by
  simpa only [normalizedVisited,visited_reflectWord] using
    normalizeVisited_reflect (visited w) (visited_nonempty w)

def reflectedClosedWord (ℓ : ℕ) : ClosedWord ℓ ≃ ClosedWord ℓ where
  toFun w := ⟨reflectWord w.val,by rw [position_reflectWord,w.property]; rfl⟩
  invFun w := ⟨reflectWord w.val,by rw [position_reflectWord,w.property]; rfl⟩
  left_inv w := Subtype.ext (reflectWord_involutive ℓ w.val)
  right_inv w := Subtype.ext (reflectWord_involutive ℓ w.val)

def firstAxisSum (ℓ : ℕ) : ℕ :=
  ∑ w : ClosedWord ℓ, firstAxisX (normalizedVisited w.val) (normalizedVisited_isNormalized _)

def bottomWidthSum (ℓ : ℕ) : ℕ :=
  ∑ w : ClosedWord ℓ, bottomWidth (normalizedVisited w.val) (normalizedVisited_isNormalized _)

def spanSum (ℓ : ℕ) : ℕ := ∑ w : ClosedWord ℓ, (normalizedVisited w.val).sup Prod.fst

theorem wordwise_reflection_identity {ℓ : ℕ} (w : ClosedWord ℓ) :
    firstAxisX (normalizedVisited w.val) (normalizedVisited_isNormalized _) +
      firstAxisX (normalizedVisited ((reflectedClosedWord ℓ w).val)) (normalizedVisited_isNormalized _) +
      bottomWidth (normalizedVisited w.val) (normalizedVisited_isNormalized _) =
        (normalizedVisited w.val).sup Prod.fst := by
  have h := firstAxis_reflection_identity (normalizedVisited_isNormalized w.val)
  simpa only [reflectedClosedWord,Equiv.coe_fn_mk,normalizedVisited_reflectWord] using h

theorem summed_reflection_identity (ℓ : ℕ) : 2 * firstAxisSum ℓ + bottomWidthSum ℓ = spanSum ℓ := by
  have h := Finset.sum_congr (rfl : (Finset.univ : Finset (ClosedWord ℓ)) = Finset.univ)
    (fun w _ => wordwise_reflection_identity w)
  simp only [Finset.sum_add_distrib] at h
  have hr : (∑ w : ClosedWord ℓ,
      firstAxisX (normalizedVisited ((reflectedClosedWord ℓ w).val)) (normalizedVisited_isNormalized _)) =
      firstAxisSum ℓ := by
    simpa only [firstAxisSum] using (reflectedClosedWord ℓ).sum_comp
      (fun w : ClosedWord ℓ => firstAxisX (normalizedVisited w.val) (normalizedVisited_isNormalized _))
  rw [hr] at h
  change firstAxisSum ℓ + firstAxisSum ℓ + bottomWidthSum ℓ = spanSum ℓ at h
  omega

theorem strip_defectSum_le_firstAxisSum (k ℓ : ℕ) :
    defectSum (horizontalStrip k) ℓ ≤ firstAxisSum ℓ := by
  apply Finset.sum_le_sum
  intro w _
  rw [normalized_defectCount_horizontalStrip (normalizedVisited_isNormalized _)]
  exact Nat.min_le_right _ _

/-- The actual finite-word inequality behind the new strip bound. -/
theorem strip_and_hitBoth_le_span (k ℓ cut : ℕ) (U A B : Diagram)
    (hA : ∀ p ∈ A, p.2 = 0 ∧ p.1 < cut)
    (hB : ∀ p ∈ B, p.2 = 0 ∧ cut ≤ p.1) :
    2 * defectSum (horizontalStrip k) ℓ +
      (∑ w : ClosedWord ℓ, (hitBothStarts U A B (normalizedVisited w.val)).card) ≤ spanSum ℓ := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (ClosedWord ℓ)))
    (fun w _ => card_hitBoth_le_bottomWidth (U := U) (normalizedVisited_isNormalized w.val) cut hA hB)
  change (∑ w : ClosedWord ℓ, (hitBothStarts U A B (normalizedVisited w.val)).card) ≤ bottomWidthSum ℓ at hsum
  have href := summed_reflection_identity ℓ
  have hstrip := strip_defectSum_le_firstAxisSum k ℓ
  omega

/-- Weighted horizontal spans of the actual closed words. -/
def spanTerm (i : ℕ) : ℝ :=
  (spanSum (i + 1) : ℝ) / ((i + 1 : ℝ) * 4 ^ (i + 1))

theorem spanSum_add_card_foundation (ℓ : ℕ) :
    spanSum ℓ + Fintype.card (ClosedWord ℓ) =
      ∑ w ∈ SquareMaximality.ClosedWalk.closedWords ℓ,
        (SquareMaximality.ClosedWalk.spanX w + 1) := by
  rw [Finset.sum_subtype _ (fun _ => SquareMaximality.ClosedWalk.mem_closedWords) _]
  rw [← (foundationClosedWordEquiv ℓ).sum_comp]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  exact foundation_spanX w.val

theorem spanTerm_add_closedWordTerm (i : ℕ) :
    spanTerm i + closedWordTerm i =
      ((∑ w ∈ SquareMaximality.ClosedWalk.closedWords (i + 1),
        (SquareMaximality.ClosedWalk.spanX w + 1) : ℕ) : ℝ) /
        ((i + 1 : ℝ) * 4 ^ (i + 1)) := by
  rw [← spanSum_add_card_foundation]
  simp only [spanTerm, closedWordTerm, Nat.cast_add, add_div]

theorem spanAndClosedTerm_even_hasSum :
    HasSum (fun i => spanTerm (2 * i) + closedWordTerm (2 * i)) (0 : ℝ) := by
  simp [spanTerm, spanSum]

theorem spanAndClosedTerm_odd_hasSum :
    HasSum (fun i => spanTerm (2 * i + 1) + closedWordTerm (2 * i + 1))
      (Real.log (4 / (1 + Real.sqrt 2))) := by
  refine SquareMaximality.Boundary.hasSum_horizontalSpanEven.congr_fun ?_
  intro i
  rw [spanTerm_add_closedWordTerm]
  simp only [show 2 * i + 1 + 1 = 2 * (i + 1) by omega,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  congr 2
  ring

/-- The full horizontal span mass is exactly entropy minus the straight-edge
constant. This transports the included span identity to our own word alphabet. -/
theorem spanTerm_hasSum :
    HasSum spanTerm
      (SquareMaximality.squareLatticeEntropy - Real.log (1 + Real.sqrt 2)) := by
  have hall := HasSum.even_add_odd (f := fun i => spanTerm i + closedWordTerm i)
    spanAndClosedTerm_even_hasSum spanAndClosedTerm_odd_hasSum
  have hsub := hall.sub closedWordTerm_hasSum
  have hlog : Real.log (4 / (1 + Real.sqrt 2)) -
      (Real.log 4 - SquareMaximality.squareLatticeEntropy) =
      SquareMaximality.squareLatticeEntropy - Real.log (1 + Real.sqrt 2) := by
    rw [Real.log_div (by norm_num) (by positivity)]
    ring
  simpa only [zero_add, add_sub_cancel_right, hlog] using hsub

/-- Fitting placements meeting an arbitrary marked face set. The bounding-box
anchor need not itself be marked. -/
def meetingStarts (U A P : Diagram) : Diagram :=
  (fittingStarts U P).filter (fun t => ∃ p ∈ P, shift t p ∈ A)

theorem foundation_meetingStarts_general {ℓ m n : ℕ} (w : Word ℓ) (V : Diagram) :
    (SquareMaximality.Boundary.walkMeetingStarts m n V (foundationWordEquiv ℓ w)).image
      foundationStartEquiv =
        meetingStarts (faceRectangle m n) (SquareMaximality.Boundary.markedFaces m n V)
          (normalizedVisited w) := by
  ext t
  simp only [Finset.mem_image, meetingStarts, Finset.mem_filter,
    foundation_fitting, SquareMaximality.Boundary.mem_walkMeetingStarts]
  constructor
  · rintro ⟨z, ⟨hx, hy, q, hq⟩, rfl⟩
    have hq' := Finset.mem_inter.mp hq
    rw [foundation_placedPartialSums w (z.1, z.2)] at hq'
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq'.1
    exact ⟨⟨hx, hy⟩, p, hp, hpq.symm ▸ hq'.2⟩
  · rintro ⟨⟨hx, hy⟩, p, hp, htp⟩
    refine ⟨foundationStartEquiv.symm t, ⟨hx, hy, shift t p, ?_⟩, by simp⟩
    apply Finset.mem_inter.mpr
    refine ⟨?_, htp⟩
    change shift t p ∈ SquareMaximality.Boundary.placedPartialSums
      (foundationWordEquiv ℓ w) t.1 t.2
    rw [foundation_placedPartialSums w t]
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

theorem foundation_closedPlacementCount_general (m n : ℕ) (V : Diagram) (ℓ : ℕ) :
    SquareMaximality.Boundary.closedPlacementCount m n V ℓ =
      ∑ w : ClosedWord ℓ,
        (meetingStarts (faceRectangle m n) (SquareMaximality.Boundary.markedFaces m n V)
          (normalizedVisited w.val)).card := by
  unfold SquareMaximality.Boundary.closedPlacementCount
  rw [Finset.sum_subtype _ (fun _ => SquareMaximality.ClosedWalk.mem_closedWords) _]
  rw [← (foundationClosedWordEquiv ℓ).sum_comp]
  apply Finset.sum_congr rfl
  intro w _
  change (SquareMaximality.Boundary.walkMeetingStarts m n V (foundationWordEquiv ℓ w.val)).card = _
  rw [← foundation_meetingStarts_general w.val V,
    Finset.card_image_of_injective _ foundationStartEquiv.injective]

theorem meetingStarts_union (U A B P : Diagram) :
    meetingStarts U (A ∪ B) P = meetingStarts U A P ∪ meetingStarts U B P := by
  ext t
  simp only [meetingStarts, Finset.mem_filter, Finset.mem_union]
  aesop

theorem meetingStarts_inter (U A B P : Diagram) :
    meetingStarts U A P ∩ meetingStarts U B P = hitBothStarts U A B P := by
  ext t
  simp only [meetingStarts, hitBothStarts, Finset.mem_filter, Finset.mem_inter]
  tauto

theorem markedFaces_union (m n : ℕ) (V W : Diagram) :
    SquareMaximality.Boundary.markedFaces m n (V ∪ W) =
      SquareMaximality.Boundary.markedFaces m n V ∪
        SquareMaximality.Boundary.markedFaces m n W := by
  ext t
  simp only [SquareMaximality.Boundary.mem_markedFaces, Finset.mem_union]
  aesop

/-- Inclusion–exclusion now counts the same fitting placements as the strip
reflection inequality, with no Ferrers condition on the marked sets. -/
theorem closedPlacementCount_inclusion_exclusion (m n : ℕ) (V W : Diagram) (ℓ : ℕ) :
    (SquareMaximality.Boundary.closedPlacementCount m n V ℓ : ℝ) +
      SquareMaximality.Boundary.closedPlacementCount m n W ℓ -
        SquareMaximality.Boundary.closedPlacementCount m n (V ∪ W) ℓ =
      ∑ w : ClosedWord ℓ,
        ((hitBothStarts (faceRectangle m n)
          (SquareMaximality.Boundary.markedFaces m n V)
          (SquareMaximality.Boundary.markedFaces m n W) (normalizedVisited w.val)).card : ℝ) := by
  simp only [foundation_closedPlacementCount_general, markedFaces_union,
    Nat.cast_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  rw [meetingStarts_union, ← meetingStarts_inter]
  have h := Finset.card_union_add_card_inter
    (meetingStarts (faceRectangle m n) (SquareMaximality.Boundary.markedFaces m n V)
      (normalizedVisited w.val))
    (meetingStarts (faceRectangle m n) (SquareMaximality.Boundary.markedFaces m n W)
      (normalizedVisited w.val))
  have hr : ((meetingStarts (faceRectangle m n) (SquareMaximality.Boundary.markedFaces m n V)
      (normalizedVisited w.val) ∪
      meetingStarts (faceRectangle m n) (SquareMaximality.Boundary.markedFaces m n W)
      (normalizedVisited w.val)).card : ℝ) +
      (meetingStarts (faceRectangle m n) (SquareMaximality.Boundary.markedFaces m n V)
      (normalizedVisited w.val) ∩
      meetingStarts (faceRectangle m n) (SquareMaximality.Boundary.markedFaces m n W)
      (normalizedVisited w.val)).card =
      (meetingStarts (faceRectangle m n) (SquareMaximality.Boundary.markedFaces m n V)
      (normalizedVisited w.val)).card +
      (meetingStarts (faceRectangle m n) (SquareMaximality.Boundary.markedFaces m n W)
      (normalizedVisited w.val)).card := by exact_mod_cast h
  linarith

def hitBothTerm (U A B : Diagram) (i : ℕ) : ℝ :=
  (∑ w : ClosedWord (i + 1), (hitBothStarts U A B (normalizedVisited w.val)).card : ℕ) /
    ((i + 1 : ℝ) * 4 ^ (i + 1))

theorem hitBothTraceTerm_eq_placements (m n : ℕ) (V W : Diagram) (i : ℕ) :
    hitBothTraceTerm (faceRectangle m n)
      (SquareMaximality.Boundary.markedFaces m n V)
      (SquareMaximality.Boundary.markedFaces m n W) i =
    hitBothTerm (faceRectangle m n)
      (SquareMaximality.Boundary.markedFaces m n V)
      (SquareMaximality.Boundary.markedFaces m n W) i := by
  have hV := faceTraceTerm_sub_eq_positivePlacementTerm m n V i
  have hW := faceTraceTerm_sub_eq_positivePlacementTerm m n W i
  have hVW := faceTraceTerm_sub_eq_positivePlacementTerm m n (V ∪ W) i
  simp only [SquareMaximality.Boundary.unmarkedFaces, foundation_faceIndices,
    markedFaces_union] at hV hW hVW
  have hc := congrArg (fun x : ℝ => x / ((i + 1 : ℝ) * 4 ^ (i + 1)))
    (closedPlacementCount_inclusion_exclusion m n V W (i + 1))
  simp only [add_div, sub_div] at hc
  unfold positivePlacementTerm at hV hW hVW
  simp only [Nat.cast_add, Nat.cast_one] at hV hW hVW
  unfold hitBothTraceTerm hitBothTerm
  rw [Nat.cast_sum]
  linarith

/-- A reusable, fully finite-volume estimate: any two separated bottom marked
sets subtract their actual Green-minor loop correlation from the strip bound. -/
theorem strip_energy_le_finite_green (k m n cut : ℕ) (V W : Diagram)
    (hV : ∀ p ∈ SquareMaximality.Boundary.markedFaces m n V, p.2 = 0 ∧ p.1 < cut)
    (hW : ∀ p ∈ SquareMaximality.Boundary.markedFaces m n W, p.2 = 0 ∧ cut ≤ p.1) :
    let A := SquareMaximality.Boundary.markedFaces m n V
    let B := SquareMaximality.Boundary.markedFaces m n W
    let hA : A ⊆ faceRectangle m n := by
      intro p hp
      exact foundation_faceIndices m n ▸ (Finset.mem_filter.mp hp).1
    let hB : B ⊆ faceRectangle m n := by
      intro p hp
      exact foundation_faceIndices m n ▸ (Finset.mem_filter.mp hp).1
    2 * realEnergy (horizontalStrip k) +
      (Real.log (Matrix.det (greenMinor hA)) + Real.log (Matrix.det (greenMinor hB)) -
        Real.log (Matrix.det (greenMinor (Finset.union_subset hA hB)))) ≤
      SquareMaximality.squareLatticeEntropy - Real.log (1 + Real.sqrt 2) := by
  dsimp only
  have hA : SquareMaximality.Boundary.markedFaces m n V ⊆ faceRectangle m n := by
    intro p hp
    exact foundation_faceIndices m n ▸ (Finset.mem_filter.mp hp).1
  have hB : SquareMaximality.Boundary.markedFaces m n W ⊆ faceRectangle m n := by
    intro p hp
    exact foundation_faceIndices m n ▸ (Finset.mem_filter.mp hp).1
  have hd : Disjoint (SquareMaximality.Boundary.markedFaces m n V)
      (SquareMaximality.Boundary.markedFaces m n W) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    have hv := hV p hp
    have hw := hW p hq
    omega
  have hseries := hitBothTraceTerm_hasSum (Finset.Subset.refl (faceRectangle m n)) hA hB hd
  have hplacements := hseries.congr_fun (fun i => (hitBothTraceTerm_eq_placements m n V W i).symm)
  apply hasSum_le _ ((realEnergy_hasSum (horizontalStrip k)).mul_left 2 |>.add hplacements)
    spanTerm_hasSum
  intro i
  unfold realEnergyTerm hitBothTerm spanTerm
  rw [← mul_div_assoc, ← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hc := strip_and_hitBoth_le_span k (i + 1) cut (faceRectangle m n)
    (SquareMaximality.Boundary.markedFaces m n V)
    (SquareMaximality.Boundary.markedFaces m n W) hV hW
  exact_mod_cast hc

/-- Two adjacent primal boundary vertices mark exactly three consecutive
boundary faces, even when this set is far from the lower-left corner. -/
theorem markedFaces_boundaryPair (m n a : ℕ) (hm : a + 2 < m) (hn : 0 < n) :
    SquareMaximality.Boundary.markedFaces m n {(a + 1, 0), (a + 2, 0)} =
      {(a, 0), (a + 1, 0), (a + 2, 0)} := by
  ext p
  simp only [SquareMaximality.Boundary.mem_markedFaces, Finset.mem_insert,
    Finset.mem_singleton, or_and_right, exists_or, exists_eq_left]
  simp only [Prod.ext_iff]
  omega

end
end SpanningTreeIsoperimetry.StripLoopBound
