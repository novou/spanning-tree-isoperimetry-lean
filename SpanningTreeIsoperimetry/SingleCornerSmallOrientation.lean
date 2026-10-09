import SpanningTreeIsoperimetry.CornerProfileNormalization
import SpanningTreeIsoperimetry.FerrersFoldTree
import SpanningTreeIsoperimetry.StripRigidity

/-! Literal diagonal polarization of a shallow Ferrers corner, with actual
primal tree counts and every corner placement. -/
namespace SpanningTreeIsoperimetry.SingleCornerSmallOrientation

open Ferrers CornerEnergy CornerFolds CornerPrimalDomains CornerProfileNormalization
open DomainIsometries Polarization StripPolarization SquareMaximality.Boundary StripRigidity
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def DiagonalDominant (M : Diagram) : Prop := ∀ p∈M, p.1≤p.2 → p.swap∈M

theorem integerFaces_transpose (M : Diagram) :
    integerFaces (transpose M)=transposeDomain (integerFaces M) := by
  unfold transpose integerFaces transposeDomain
  rw [Finset.image_image,Finset.image_image]
  congr 1

theorem dominant_integer {M : Diagram} (hM : DiagonalDominant M) :
    ∀ p∈integerFaces M, p.1≤p.2 → p.swap∈integerFaces M := by
  intro p hp hxy
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  have hqxy : q.1≤q.2 := by
    change (q.1 : ℤ)≤q.2 at hxy
    exact_mod_cast hxy
  exact Finset.mem_image.mpr ⟨q.swap,hM q hq hqxy,rfl⟩

/-- Polarizing the transposed vacancy diagram gives the original diagram. -/
theorem polarize_transposed_defect {u v : ℕ} (huv : u≤v) (D : Domain)
    (hfit : D⊆rectangle u u) (hdom : ∀ p∈D, p.1≤p.2 → p.swap∈D) :
    polarized (rectangle u v\transposeDomain D) Prod.swap (fun p : Vertex => p.1<p.2)=
      rectangle u v\D := by
  ext p
  rw [mem_polarized Prod.swap_swap]
  simp only [Finset.mem_sdiff,mem_transposeDomain,Prod.swap_swap]
  by_cases hp : p.1<p.2
  · simp only [hp,ite_true]
    constructor
    · rintro (⟨hr,hn⟩ | ⟨hr,hn⟩)
      · exact ⟨hr,fun hm => hn (hdom p hm hp.le)⟩
      · refine ⟨?_,hn⟩
        have h := mem_rectangle.mp hr
        apply mem_rectangle.mpr
        dsimp only [Prod.fst_swap,Prod.snd_swap] at h
        omega
    · rintro ⟨hr,hn⟩
      by_cases hd : p.swap∈D
      · right
        refine ⟨?_,hn⟩
        have h := mem_rectangle.mp (hfit hd)
        apply mem_rectangle.mpr
        dsimp only [Prod.fst_swap,Prod.snd_swap] at h ⊢
        omega
      · exact Or.inl ⟨hr,hd⟩
  · simp only [hp,ite_false]
    constructor
    · rintro ⟨⟨hr,_⟩,⟨_,hn⟩⟩
      exact ⟨hr,hn⟩
    · rintro ⟨hr,hn⟩
      have hswap : p.swap∈rectangle u v := by
        have h := mem_rectangle.mp hr
        apply mem_rectangle.mpr
        dsimp only [Prod.fst_swap,Prod.snd_swap]
        omega
      have hnot : p.swap∉D := by
        intro hd
        have h := hdom p.swap hd (by dsimp only [Prod.fst_swap,Prod.snd_swap]; omega)
        exact hn (by simpa only [Prod.swap_swap] using h)
      exact ⟨⟨hr,hnot⟩,⟨hswap,hn⟩⟩

theorem singleFamily_ferrers (c : Corner) {M : Diagram} (hM : IsFerrers M) :
    ∀ d, IsFerrers (singleFamily c M d) :=
  twoCornerFamily_ferrers c (opposite c) hM empty_ferrers

theorem singleFamily_total (c : Corner) (M : Diagram) : totalDefect (singleFamily c M)=M.card := by
  rw [singleFamily,totalDefect_twoCornerFamily (opposite_distinct c)]
  simp

theorem single_card {u v : ℕ} (c : Corner) {M : Diagram} (hM : IsFerrers M)
    (hu : M.card≤u) (hv : M.card≤v) :
    (cornerPrimal u v (singleFamily c M)).card=(u+1)*(v+1)-M.card := by
  simpa only [singleFamily_total] using cornerPrimal_card (singleFamily_ferrers c hM)
    (by rw [singleFamily_total]; exact hu) (by rw [singleFamily_total]; exact hv)

theorem card_le_extents (M : Diagram) : M.card≤ferrersWidth M*ferrersHeight M := by
  have hsub : M⊆faceRectangle (ferrersWidth M) (ferrersHeight M) := by
    intro p hp
    exact mem_faceRectangle.mpr (ferrers_extent_bounds hp)
  have h := Finset.card_le_card hsub
  simpa [faceRectangle] using h

theorem width_gt_of_two_rows {M : Diagram} {d : ℕ} (hh : ferrersHeight M≤2)
    (hk : 2*d<M.card) : d<ferrersWidth M := by
  have hc := card_le_extents M
  have hm := Nat.mul_le_mul_left (ferrersWidth M) hh
  nlinarith

theorem single_face_count {u v : ℕ} (hu : 1≤u) (huv : u≤v) {M : Diagram}
    (hM : IsFerrers M) (hk : M.card≤u) :
    (treeCount (cornerPrimal u v (singleFamily (true,true) M)) : ℝ)=
      faceDeterminant (rectangle u v\integerFaces M) 4 := by
  have h := cornerPrimal_treeCount_eq_faceDeterminant hu (by omega : 1≤v)
    (singleFamily_ferrers (true,true) hM)
    (by rw [singleFamily_total]; exact hk) (by rw [singleFamily_total]; omega)
  have hf : cornerFaceDomain u v (singleFamily (true,true) M)=rectangle u v\integerFaces M := by
    unfold cornerFaceDomain
    rw [vacancies_single]
    unfold integerFaces
    rw [Finset.image_sdiff _ _ ofNatPoint_injective]
    change integerFaces (faceRectangle u v)\integerFaces M=rectangle u v\integerFaces M
    rw [CornerStripBridge.integerFaces_faceRectangle]
  rw [hf] at h
  exact h

theorem dominant_transpose_treeCount {u v : ℕ} (hu : 1≤u) (huv : u≤v) {M : Diagram}
    (hM : IsFerrers M) (hk : M.card≤u) (hdom : DiagonalDominant M) (c : Corner) :
    treeCount (cornerPrimal u v (singleFamily c M))≤
      treeCount (cornerPrimal u v (singleFamily c (transpose M))) := by
  have hfit : integerFaces M⊆rectangle u u := by
    rw [← CornerStripBridge.integerFaces_faceRectangle]
    exact Finset.image_subset_image (ferrers_fit_of_card hM hk hk)
  have hpol := polarize_transposed_defect huv (integerFaces M) hfit (dominant_integer hdom)
  rw [← integerFaces_transpose] at hpol
  let U := rectangle u v\integerFaces (transpose M)
  have hd := adjacency_determinant_of_domain_moments U
    (polarized U Prod.swap (fun p : Vertex => p.1<p.2))
    (card_polarized Prod.swap_swap _ diagonal_preferred_side).symm
    (fun i => diagonal_adjacency_moments U (i+1)) 4 le_rfl
  change faceDeterminant (polarized U Prod.swap (fun p : Vertex => p.1<p.2)) 4≤faceDeterminant U 4 at hd
  dsimp only [U] at hd
  rw [hpol,← single_face_count hu huv hM hk,
    ← single_face_count hu huv (transpose_isFerrers hM) (by simpa only [card_transpose] using hk)] at hd
  have hn := (single_normalization (R := u) (S := v) c hM hk (hk.trans huv)).treeCount_eq
  have hnt := (single_normalization (R := u) (S := v) c (transpose_isFerrers hM)
    (by simpa only [card_transpose] using hk) (by simpa only [card_transpose] using hk.trans huv)).treeCount_eq
  rw [hn,hnt]
  exact_mod_cast hd

theorem transpose_height (M : Diagram) : ferrersHeight (transpose M)=ferrersWidth M := by
  simp [ferrersHeight,ferrersWidth,transpose,Finset.sup_image,Function.comp_def]

theorem transpose_width (M : Diagram) : ferrersWidth (transpose M)=ferrersHeight M := by
  simp [ferrersHeight,ferrersWidth,transpose,Finset.sup_image,Function.comp_def]

/-- A genuine two-row nonstrip has all its unmatched cells below the diagonal. -/
theorem two_row_dominant {M : Diagram} (hM : IsFerrers M)
    (hh : ferrersHeight M≤2) (hw : 2≤ferrersWidth M) : DiagonalDominant M := by
  intro p hp hxy
  rcases p with ⟨x,y⟩
  have hy := (ferrers_extent_bounds hp).2
  dsimp only [Prod.fst,Prod.snd] at hxy hy
  by_cases he : x=y
  · simpa only [Prod.swap,he] using hp
  · have hx0 : x=0 := by omega
    have hy1 : y=1 := by omega
    have hc := ferrers_width_corner hM ⟨(x,y),hp⟩
    have h10 : (1,0)∈M := hM _ hc (1,0) (by omega) (by omega)
    simpa only [Prod.swap,hx0,hy1] using h10

theorem transpose_nonstrip {M : Diagram} (hn : ¬IsStraightStrip M) : ¬IsStraightStrip (transpose M) := by
  rintro (h|h)
  · have hh := congrArg transpose h
    have he : M=transpose (horizontalStrip M.card) := by
      simpa only [transpose_transpose,card_transpose] using hh
    exact hn (Or.inr he)
  · have hh := congrArg transpose h
    have he : M=horizontalStrip M.card := by
      simpa only [transpose_transpose,card_transpose] using hh
    exact hn (Or.inl he)

theorem two_row_transpose_treeCount {u v : ℕ} (hu : 1≤u) (huv : u≤v) {M : Diagram}
    (hM : IsFerrers M) (hk : M.card≤u) (hn : ¬IsStraightStrip M) (hh : ferrersHeight M≤2) (c : Corner) :
    treeCount (cornerPrimal u v (singleFamily c M))≤
      treeCount (cornerPrimal u v (singleFamily c (transpose M))) := by
  have hext := ferrers_nonstrip_extents hM (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h))
  exact dominant_transpose_treeCount hu huv hM hk (two_row_dominant hM hh hext.1) c

end
end SpanningTreeIsoperimetry.SingleCornerSmallOrientation
