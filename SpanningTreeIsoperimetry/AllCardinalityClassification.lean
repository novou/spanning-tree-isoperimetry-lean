import SpanningTreeIsoperimetry.LargeClassification

/-! Complete actual maximum values, equality classes and nonuniqueness at
all positive cardinalities, combining the large and small classifications. -/
namespace SpanningTreeIsoperimetry.AllCardinalityClassification
open SmallMaximizerClassification
noncomputable section

theorem maximumValueTarget : MaximumValueTarget :=
  ClassificationAssembly.maximum_value_of_unique_classification LargeClassification.uniqueClassificationTarget

theorem nonuniquenessTarget : NonuniquenessTarget :=
  ClassificationAssembly.nonuniqueness_of_unique_classification LargeClassification.uniqueClassificationTarget

def MaximizerForm (N : ℕ) (A : Domain) : Prop :=
  if N≤17 then SmallForm N A else Congruent A (canonicalDomain N)

theorem maximizer_iff {A : Domain} (hN : 0<A.card) :
    IsMaximizer A ↔ MaximizerForm A.card A := by
  by_cases hs : A.card≤17
  · simpa only [MaximizerForm,if_pos hs] using small_maximizer_iff hN hs
  · simpa only [MaximizerForm,if_neg hs] using LargeClassification.maximizer_iff (by omega : 18≤A.card)

end
end SpanningTreeIsoperimetry.AllCardinalityClassification
