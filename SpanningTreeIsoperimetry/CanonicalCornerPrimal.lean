import SpanningTreeIsoperimetry.CornerPrimalFaces
import SpanningTreeIsoperimetry.Isoperimetry

/-! The actual four-corner decomposition of a normalized maximizing domain
is exactly the explicit primal family used by the fold comparisons. -/
namespace SpanningTreeIsoperimetry.CornerPrimalDomains

open Ferrers CornerEnergy DomainIsometries SquareMaximality.Boundary FerrersPrimalBridge
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def canonicalCornerFamily (A : Domain) (R S : ℕ) : Corner → Diagram :=
  fun c => cornerDiagram A (R+1) (S+1) c.1 c.2

theorem canonicalCorner_ferrers (A : Domain) (R S : ℕ) :
    ∀ c, IsFerrers (canonicalCornerFamily A R S c) :=
  fun c => cornerDiagram_isFerrers A (R+1) (S+1) c.1 c.2

theorem canonicalCorner_fit (A : Domain) (R S : ℕ) (c : Corner) :
    canonicalCornerFamily A R S c⊆faceRectangle (R+1) (S+1) := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

theorem canonicalCorner_integer_image (A : Domain) (R S : ℕ) (c : Corner) :
    integerFaces (placedCorner R S c (canonicalCornerFamily A R S c))=
      cornerVacancies A (R+1) (S+1) c.1 c.2 := by
  rw [integerFaces_placedCorner c (canonicalCorner_fit A R S c)]
  have he : (fun p : Ferrers.Point =>
      ((if c.1 then (p.1 : ℤ) else (R : ℤ)-p.1),(if c.2 then (p.2 : ℤ) else (S : ℤ)-p.2)))=
      cornerEmbedding (R+1) (S+1) c.1 c.2 := by
    funext p
    rcases c with ⟨cx,cy⟩
    cases cx <;> cases cy <;> simp [cornerEmbedding]
  rw [he]
  exact cornerDiagram_image A (R+1) (S+1) c.1 c.2

theorem cornerVacancies_union {A : Domain} {R S : ℕ}
    (hh : IsStandardHull A (R+1) (S+1)) (hconn : (domainGraph A).Connected)
    (hrow : IsRowConvex A) (hcol : IsColumnConvex A) :
    (Finset.univ.biUnion fun c : Corner => cornerVacancies A (R+1) (S+1) c.1 c.2)=
      rectangle (R+1) (S+1) \ A := by
  ext p
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨c,hc⟩
    have h := mem_cornerVacancies.mp hc
    exact Finset.mem_sdiff.mpr ⟨h.1,cornerEmpty_not_mem h.2⟩
  · intro hp
    obtain ⟨c,hc,_⟩ := (four_corner_partition hh hconn hrow hcol p).mp hp
    exact ⟨c,hc⟩

theorem canonical_integer_vacancies {A : Domain} {R S : ℕ}
    (hh : IsStandardHull A (R+1) (S+1)) (hconn : (domainGraph A).Connected)
    (hrow : IsRowConvex A) (hcol : IsColumnConvex A) :
    integerFaces (fourCornerVacancies R S (canonicalCornerFamily A R S))=
      rectangle (R+1) (S+1) \ A := by
  unfold integerFaces fourCornerVacancies
  rw [Finset.biUnion_image]
  change (Finset.univ.biUnion fun c => integerFaces (placedCorner R S c (canonicalCornerFamily A R S c)))=_
  simp_rw [canonicalCorner_integer_image]
  exact cornerVacancies_union hh hconn hrow hcol

theorem canonicalCornerPrimal_eq {A : Domain} {R S : ℕ}
    (hh : IsStandardHull A (R+1) (S+1)) (hconn : (domainGraph A).Connected)
    (hrow : IsRowConvex A) (hcol : IsColumnConvex A) :
    cornerPrimal R S (canonicalCornerFamily A R S)=A := by
  rw [cornerPrimal,primalDomain_eq,canonical_integer_vacancies hh hconn hrow hcol]
  ext p
  simp only [Finset.mem_sdiff]
  constructor
  · rintro ⟨hp,hn⟩
    by_contra hnot
    exact hn ⟨hp,hnot⟩
  · intro hp
    exact ⟨hh.subset hp,fun hn => hn.2 hp⟩

theorem canonicalCorner_total {A : Domain} {R S : ℕ}
    (hh : IsStandardHull A (R+1) (S+1)) (hconn : (domainGraph A).Connected)
    (hrow : IsRowConvex A) (hcol : IsColumnConvex A) :
    totalDefect (canonicalCornerFamily A R S)=(R+1)*(S+1)-A.card := by
  have hdisj : (↑(Finset.univ : Finset Corner) : Set Corner).PairwiseDisjoint
      (fun c => cornerVacancies A (R+1) (S+1) c.1 c.2) := by
    intro c _ d _ hcd
    apply Finset.disjoint_left.mpr
    intro p hc hd
    have hb := mem_cornerVacancies.mp hc
    have hp : p∈rectangle (R+1) (S+1) \ A :=
      Finset.mem_sdiff.mpr ⟨hb.1,cornerEmpty_not_mem hb.2⟩
    obtain ⟨e,he,hunique⟩ := (four_corner_partition hh hconn hrow hcol p).mp hp
    exact hcd ((hunique c hc).trans (hunique d hd).symm)
  have hcard := congrArg Finset.card (cornerVacancies_union hh hconn hrow hcol)
  rw [Finset.card_biUnion hdisj,Finset.card_sdiff_of_subset hh.subset,card_rectangle] at hcard
  unfold totalDefect
  rw [← hcard]
  apply Finset.sum_congr rfl
  intro c _
  rw [← cornerDiagram_image A (R+1) (S+1) c.1 c.2,
    Finset.card_image_of_injective _ (cornerEmbedding_injective (R+1) (S+1) c.1 c.2)]
  rfl

/-- No shape assumption is supplied: a normalized maximizer is exactly one
of the concrete sparse four-corner primal domains. -/
theorem maximizer_canonicalCorner_model {A : Domain} {R S : ℕ} (hmax : IsMaximizer A)
    (hh : IsStandardHull A (R+1) (S+1)) :
    A=cornerPrimal R S (canonicalCornerFamily A R S) ∧
      (∀ c, IsFerrers (canonicalCornerFamily A R S c)) ∧
      totalDefect (canonicalCornerFamily A R S)≤R ∧
      totalDefect (canonicalCornerFamily A R S)≤S := by
  have hf := standardHull_to_foundation hh
  have hshape := maximizer_hull_shape hmax hf
  have hdef := maximizer_deficit_lt_min_side hmax hf
  have htotal := canonicalCorner_total hh hmax.1 hshape.1 hshape.2.1
  refine ⟨(canonicalCornerPrimal_eq hh hmax.1 hshape.1 hshape.2.1).symm,
    canonicalCorner_ferrers A R S,?_,?_⟩ <;> omega

end
end SpanningTreeIsoperimetry.CornerPrimalDomains
