import SpanningTreeIsoperimetry.Grid
import SpanningTreeIsoperimetry.HullArithmetic
import Mathlib.Data.Finset.SymmDiff

open scoped symmDiff

namespace SpanningTreeIsoperimetry

def translatedSquare (n : ℕ) (a : Vertex) : Domain :=
  (rectangle n n).image (translate a)

@[simp] theorem card_translatedSquare (n : ℕ) (a : Vertex) :
    (translatedSquare n a).card = n ^ 2 := by
  rw [translatedSquare, Finset.card_image_of_injective _ (translate_injective a)]
  simp [pow_two]

@[simp] theorem mem_translatedSquare {n : ℕ} {a v : Vertex} :
    v ∈ translatedSquare n a ↔
      a.1 ≤ v.1 ∧ v.1 < a.1 + n ∧ a.2 ≤ v.2 ∧ v.2 < a.2 + n := by
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    simp only [mem_rectangle] at hw
    simp only [translate]
    omega
  · intro hv
    apply Finset.mem_image.mpr
    refine ⟨(v.1 - a.1, v.2 - a.2), ?_, ?_⟩
    · simp only [mem_rectangle]
      omega
    · simp [translate]

@[simp] theorem translatedSquare_zero (n : ℕ) :
    translatedSquare n (0, 0) = rectangle n n := by
  ext v
  simp

/-- Equal cardinalities turn symmetric difference into twice the number of
points outside the comparison set. -/
theorem card_symmDiff_of_card_eq {S Q : Domain} (hcard : S.card = Q.card) :
    (S ∆ Q).card = 2 * (S \ Q).card := by
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
  · have hdiff := Finset.card_sdiff_comm hcard
    omega
  · exact Finset.disjoint_left.mpr fun _ hv hw =>
      (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mp hw).1

theorem rectangle_inter_rectangle (r s R T : ℕ) :
    rectangle r s ∩ rectangle R T = rectangle (min r R) (min s T) := by
  ext v
  simp only [Finset.mem_inter, mem_rectangle, Nat.cast_min]
  constructor <;> intro h <;> constructor
  all_goals aesop

/-- A short-side hull loses at most `r(s-n)` points outside the origin square. -/
theorem mixed_hull_outside_bound {S : Domain} {n r s : ℕ}
    (hS : S ⊆ rectangle r s) (hr : r ≤ n) (hs : n ≤ s) :
    (S \ rectangle n n).card ≤ r * (s - n) := by
  have hsub : S \ rectangle n n ⊆ rectangle r s \ rectangle n n := by
    intro v hv
    simp only [Finset.mem_sdiff] at hv ⊢
    exact ⟨hS hv.1, hv.2⟩
  have hcard := Finset.card_le_card hsub
  have hinter : rectangle n n ∩ rectangle r s = rectangle r n := by
    rw [rectangle_inter_rectangle, min_eq_right hr, min_eq_left hs]
  rw [Finset.card_sdiff (s := rectangle n n) (t := rectangle r s),
    hinter, card_rectangle, card_rectangle] at hcard
  have hprod : r * n ≤ r * s := Nat.mul_le_mul_left r hs
  have hsubn : s - n + n = s := Nat.sub_add_cancel hs
  have hsubp : r * s - r * n + r * n = r * s := Nat.sub_add_cancel hprod
  have hidentity : r * s - r * n = r * (s - n) := by nlinarith
  simpa only [hidentity] using hcard

/-- When the origin square lies in the hull, the hull's excess area bounds
the number of points outside it. -/
theorem large_hull_outside_bound {S : Domain} {n r s : ℕ}
    (hS : S ⊆ rectangle r s) (hr : n ≤ r) (hs : n ≤ s) :
    (S \ rectangle n n).card ≤ r * s - n ^ 2 := by
  have hsub : S \ rectangle n n ⊆ rectangle r s \ rectangle n n := by
    intro v hv
    simp only [Finset.mem_sdiff] at hv ⊢
    exact ⟨hS hv.1, hv.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset (rectangle_mono hr hs), card_rectangle,
    card_rectangle] at hcard
  simpa only [pow_two] using hcard

/-- Four corner-anchored squares cover a rectangle with sides at most `2n`.
The sides need not be minimal, and no connectedness assumption is needed. -/
theorem four_corner_squares_cover {n r s : ℕ}
    (_hr : n ≤ r) (_hs : n ≤ s) (hr2 : r ≤ 2 * n) (hs2 : s ≤ 2 * n) :
    rectangle r s ⊆
      translatedSquare n (0, 0) ∪ translatedSquare n ((r : ℤ) - n, 0) ∪
      translatedSquare n (0, (s : ℤ) - n) ∪
      translatedSquare n ((r : ℤ) - n, (s : ℤ) - n) := by
  intro v hv
  simp only [mem_rectangle] at hv
  simp only [Finset.mem_union, mem_translatedSquare]
  have hr' : (r : ℤ) ≤ 2 * n := by exact_mod_cast hr2
  have hs' : (s : ℤ) ≤ 2 * n := by exact_mod_cast hs2
  omega

/-- A finite-set pigeonhole statement for four covering sets. -/
theorem four_cover_large_intersection {S A B C D : Domain}
    (hcover : S ⊆ A ∪ B ∪ C ∪ D) :
    S.card ≤ 4 * (S ∩ A).card ∨ S.card ≤ 4 * (S ∩ B).card ∨
    S.card ≤ 4 * (S ∩ C).card ∨ S.card ≤ 4 * (S ∩ D).card := by
  have hsub : S ⊆ (S ∩ A) ∪ (S ∩ B) ∪ (S ∩ C) ∪ (S ∩ D) := by
    intro v hv
    have hv' := hcover hv
    simp only [Finset.mem_union, Finset.mem_inter] at hv' ⊢
    tauto
  have hcard := Finset.card_le_card hsub
  have h₁ := Finset.card_union_le (S ∩ A) (S ∩ B)
  have h₂ := Finset.card_union_le ((S ∩ A) ∪ (S ∩ B)) (S ∩ C)
  have h₃ := Finset.card_union_le ((S ∩ A) ∪ (S ∩ B) ∪ (S ∩ C)) (S ∩ D)
  omega

/-- One of the four corner squares contains at least one quarter of the set. -/
theorem exists_corner_square_quarter {S : Domain} {n r s : ℕ}
    (hS : S ⊆ rectangle r s) (hr : n ≤ r) (hs : n ≤ s)
    (hr2 : r ≤ 2 * n) (hs2 : s ≤ 2 * n) :
    ∃ a : Vertex, S.card ≤ 4 * (S ∩ translatedSquare n a).card := by
  have hcover := Finset.Subset.trans hS (four_corner_squares_cover hr hs hr2 hs2)
  rcases four_cover_large_intersection hcover with h | h | h | h
  · exact ⟨(0, 0), h⟩
  · exact ⟨((r : ℤ) - n, 0), h⟩
  · exact ⟨(0, (s : ℤ) - n), h⟩
  · exact ⟨((r : ℤ) - n, (s : ℤ) - n), h⟩

/-- The actual finite-set geometric estimate before squaring: after ordering
the hull sides, a translate of the `n`-square misses at most the indicated
number of vertices. No spanning-tree hypothesis is used. -/
theorem exists_square_outside_bound_ordered {S : Domain} {n r s : ℕ}
    (hn : 0 < n) (hcard : S.card = n ^ 2) (hS : S ⊆ rectangle r s)
    (hrs : r ≤ s) :
    ∃ a : Vertex, ((S \ translatedSquare n a).card : ℝ) ≤
      (n : ℝ) ^ 2 * Real.sqrt (((r : ℝ) + s - 2 * n) / n) := by
  have harea : n ^ 2 ≤ r * s := by
    simpa only [hcard, card_rectangle] using Finset.card_le_card hS
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have harea' : (n : ℝ) ^ 2 ≤ (r : ℝ) * s := by exact_mod_cast harea
  have hrs' : (r : ℝ) ≤ s := by exact_mod_cast hrs
  have hp : 0 ≤ (r : ℝ) + s - 2 * n := by
    nlinarith [sq_nonneg ((r : ℝ) - s), Nat.cast_nonneg (α := ℝ) r,
      Nat.cast_nonneg (α := ℝ) s]
  let x : ℝ := ((r : ℝ) + s - 2 * n) / n
  have hx : 0 ≤ x := div_nonneg hp hn'.le
  have hn2 : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hn'
  by_cases hbig : 1 ≤ x
  · refine ⟨(0, 0), ?_⟩
    have hout : (S \ translatedSquare n (0, 0)).card ≤ n ^ 2 := by
      rw [← hcard]
      exact Finset.card_le_card Finset.sdiff_subset
    have hout' : ((S \ translatedSquare n (0, 0)).card : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast hout
    have hroot : 1 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by simpa using hbig)
    have hmul := mul_le_mul_of_nonneg_left hroot hn2.le
    change ((S \ translatedSquare n (0, 0)).card : ℝ) ≤ (n : ℝ) ^ 2 * Real.sqrt x
    nlinarith
  have hx1 : x ≤ 1 := by linarith
  have hp_small : (r : ℝ) + s - 2 * n ≤ n := by
    exact (div_le_one hn').mp hx1
  by_cases hrn : r ≤ n
  · have hsn : n ≤ s := by nlinarith
    have hrn' : (r : ℝ) ≤ n := by exact_mod_cast hrn
    have hsn' : (n : ℝ) ≤ s := by exact_mod_cast hsn
    let y : ℝ := ((n : ℝ) - r) / n
    have hy : 0 ≤ y := div_nonneg (sub_nonneg.mpr hrn') hn'.le
    have hyarea : y ^ 2 ≤ x * (1 - y) := by
      apply (mul_le_mul_iff_of_pos_right hn2).mp
      have hid₁ : y ^ 2 * (n : ℝ) ^ 2 = ((n : ℝ) - r) ^ 2 := by
        dsimp [y]
        field_simp
      have hid₂ : x * (1 - y) * (n : ℝ) ^ 2 =
          ((r : ℝ) + s - 2 * n) * r := by
        dsimp [x, y]
        field_simp
        ring
      rw [hid₁, hid₂]
      nlinarith
    have hscalar := stability_mixed_side_bound hx hx1 hy hyarea
    have hscaled := mul_le_mul_of_nonneg_right hscalar hn2.le
    have hid : (1 - y) * (x + y) * (n : ℝ) ^ 2 = (r : ℝ) * (s - n) := by
      dsimp [x, y]
      field_simp
      ring
    rw [hid] at hscaled
    have hout := mixed_hull_outside_bound hS hrn hsn
    have hout' : ((S \ rectangle n n).card : ℝ) ≤ (r : ℝ) * (s - n) := by
      exact_mod_cast hout
    refine ⟨(0, 0), ?_⟩
    rw [translatedSquare_zero]
    change ((S \ rectangle n n).card : ℝ) ≤ (n : ℝ) ^ 2 * Real.sqrt x
    nlinarith
  · have hnr : n ≤ r := by omega
    have hns : n ≤ s := le_trans hnr hrs
    have hnr' : (n : ℝ) ≤ r := by exact_mod_cast hnr
    have hns' : (n : ℝ) ≤ s := by exact_mod_cast hns
    have hr2 : r ≤ 2 * n := by exact_mod_cast (show (r : ℝ) ≤ 2 * n by linarith)
    have hs2 : s ≤ 2 * n := by exact_mod_cast (show (s : ℝ) ≤ 2 * n by linarith)
    have hscalar := stability_min_bound hx
    by_cases hmin : x + x ^ 2 / 4 ≤ 3 / 4
    · rw [min_eq_left hmin] at hscalar
      have hscaled := mul_le_mul_of_nonneg_left hscalar hn2.le
      have hid : (n : ℝ) ^ 2 * (x + x ^ 2 / 4) =
          (n : ℝ) * ((r : ℝ) + s - 2 * n) + ((r : ℝ) + s - 2 * n) ^ 2 / 4 := by
        dsimp [x]
        field_simp
      rw [hid] at hscaled
      have hout := large_hull_outside_bound hS hnr hns
      have hout' : ((S \ rectangle n n).card : ℝ) ≤ (r : ℝ) * s - n ^ 2 := by
        exact_mod_cast hout
      refine ⟨(0, 0), ?_⟩
      rw [translatedSquare_zero]
      change ((S \ rectangle n n).card : ℝ) ≤ (n : ℝ) ^ 2 * Real.sqrt x
      nlinarith [sq_nonneg ((r : ℝ) - s)]
    · rw [min_eq_right (le_of_not_ge hmin)] at hscalar
      obtain ⟨a, ha⟩ := exists_corner_square_quarter hS hnr hns hr2 hs2
      have hparts := Finset.card_sdiff_add_card_inter S (translatedSquare n a)
      have hout : 4 * (S \ translatedSquare n a).card ≤ 3 * n ^ 2 := by omega
      have hout' : 4 * ((S \ translatedSquare n a).card : ℝ) ≤ 3 * (n : ℝ) ^ 2 := by
        exact_mod_cast hout
      have hscaled := mul_le_mul_of_nonneg_left hscalar hn2.le
      refine ⟨a, ?_⟩
      change ((S \ translatedSquare n a).card : ℝ) ≤ (n : ℝ) ^ 2 * Real.sqrt x
      nlinarith

theorem transposeDomain_subset_rectangle {S : Domain} {r s : ℕ}
    (hS : S ⊆ rectangle r s) : transposeDomain S ⊆ rectangle s r := by
  intro v hv
  have hw := hS (mem_transposeDomain.mp hv)
  simp only [mem_rectangle] at hw ⊢
  exact ⟨hw.2.2.1, hw.2.2.2, hw.1, hw.2.1⟩

theorem transposeDomain_sdiff_square (S : Domain) (n : ℕ) (a : Vertex) :
    transposeDomain S \ translatedSquare n a =
      transposeDomain (S \ translatedSquare n a.swap) := by
  ext v
  simp only [Finset.mem_sdiff, mem_transposeDomain, mem_translatedSquare,
    Prod.fst_swap, Prod.snd_swap]
  tauto

/-- The geometric outside-point bound with no ordering restriction on the
rectangle. Coordinate transposition supplies the other orientation. -/
theorem exists_square_outside_bound {S : Domain} {n r s : ℕ}
    (hn : 0 < n) (hcard : S.card = n ^ 2) (hS : S ⊆ rectangle r s) :
    ∃ a : Vertex, ((S \ translatedSquare n a).card : ℝ) ≤
      (n : ℝ) ^ 2 * Real.sqrt (((r : ℝ) + s - 2 * n) / n) := by
  by_cases hrs : r ≤ s
  · exact exists_square_outside_bound_ordered hn hcard hS hrs
  · have hsr : s ≤ r := by omega
    have hcard' : (transposeDomain S).card = n ^ 2 := by simpa using hcard
    obtain ⟨a, ha⟩ := exists_square_outside_bound_ordered hn hcard'
      (transposeDomain_subset_rectangle hS) hsr
    rw [transposeDomain_sdiff_square, card_transposeDomain] at ha
    refine ⟨a.swap, ?_⟩
    simpa only [add_comm (s : ℝ) r] using ha

/-- The unnormalized form of manuscript `lem:geometric-asymmetry`.
It holds for every `n²`-point subset of the rectangle, not just connected sets
or minimal rectangular hulls. Dividing by `n⁴` gives the stated bound on the
square of normalized translational asymmetry. -/
theorem exists_square_symmDiff_sq_bound {S : Domain} {n r s : ℕ}
    (hn : 0 < n) (hcard : S.card = n ^ 2) (hS : S ⊆ rectangle r s) :
    ∃ a : Vertex, ((S ∆ translatedSquare n a).card : ℝ) ^ 2 ≤
      4 * (n : ℝ) ^ 3 * ((r : ℝ) + s - 2 * n) := by
  obtain ⟨a, ha⟩ := exists_square_outside_bound hn hcard hS
  refine ⟨a, ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have harea : n ^ 2 ≤ r * s := by
    simpa only [hcard, card_rectangle] using Finset.card_le_card hS
  have harea' : (n : ℝ) ^ 2 ≤ (r : ℝ) * s := by exact_mod_cast harea
  have hp : 0 ≤ (r : ℝ) + s - 2 * n := by
    nlinarith [sq_nonneg ((r : ℝ) - s), Nat.cast_nonneg (α := ℝ) r,
      Nat.cast_nonneg (α := ℝ) s]
  have hx : 0 ≤ ((r : ℝ) + s - 2 * n) / n := div_nonneg hp hn'.le
  have hsq := (sq_le_sq₀ (by positivity) (by positivity)).mpr ha
  have hid : ((n : ℝ) ^ 2 * Real.sqrt (((r : ℝ) + s - 2 * n) / n)) ^ 2 =
      (n : ℝ) ^ 3 * ((r : ℝ) + s - 2 * n) := by
    rw [mul_pow, Real.sq_sqrt hx]
    field_simp
  rw [hid] at hsq
  have hcards : S.card = (translatedSquare n a).card := by simp [hcard]
  have hdiff : ((S ∆ translatedSquare n a).card : ℝ) =
      2 * ((S \ translatedSquare n a).card : ℝ) := by
    exact_mod_cast card_symmDiff_of_card_eq hcards
  nlinarith

/-- Translation of a finite lattice domain. -/
def translateDomain (a : Vertex) (S : Domain) : Domain := S.image (translate a)

@[simp] theorem card_translateDomain (a : Vertex) (S : Domain) :
    (translateDomain a S).card = S.card :=
  Finset.card_image_of_injective _ (translate_injective a)

@[simp] theorem translateDomain_zero (S : Domain) : translateDomain (0, 0) S = S := by
  have hfun : translate (0, 0) = id := by
    funext v
    simp [translate]
  rw [translateDomain, hfun, Finset.image_id]

theorem translateDomain_add (a b : Vertex) (S : Domain) :
    translateDomain a (translateDomain b S) = translateDomain (a + b) S := by
  simp only [translateDomain, Finset.image_image]
  congr 1
  funext v
  simp [translate, add_assoc]

theorem translateDomain_symmDiff (a : Vertex) (S T : Domain) :
    translateDomain a (S ∆ T) = translateDomain a S ∆ translateDomain a T :=
  Finset.image_symmDiff S T (translate_injective a)

theorem translateDomain_square (a b : Vertex) (n : ℕ) :
    translateDomain a (translatedSquare n b) = translatedSquare n (a + b) :=
  translateDomain_add a b (rectangle n n)

/-- A finite domain fits a rectangle without fixing the rectangle's position. -/
def FitsRectangle (S : Domain) (r s : ℕ) : Prop :=
  ∃ a : Vertex, S ⊆ (rectangle r s).image (translate a)

theorem translateDomain_neg_subset_rectangle {S : Domain} {r s : ℕ} {a : Vertex}
    (hS : S ⊆ (rectangle r s).image (translate a)) :
    translateDomain (-a) S ⊆ rectangle r s := by
  have hsub := Finset.image_subset_image (f := translate (-a)) hS
  change translateDomain (-a) S ⊆ translateDomain (-a) (translateDomain a (rectangle r s)) at hsub
  rw [translateDomain_add, neg_add_cancel] at hsub
  simpa only [show (0 : Vertex) = (0, 0) from rfl, translateDomain_zero] using hsub

/-- Translation-invariant version of the full geometric asymmetry estimate.
The containing rectangle may have any lattice origin. -/
theorem exists_square_symmDiff_sq_bound_of_fits {S : Domain} {n r s : ℕ}
    (hn : 0 < n) (hcard : S.card = n ^ 2) (hS : FitsRectangle S r s) :
    ∃ a : Vertex, ((S ∆ translatedSquare n a).card : ℝ) ^ 2 ≤
      4 * (n : ℝ) ^ 3 * ((r : ℝ) + s - 2 * n) := by
  obtain ⟨a, ha⟩ := hS
  have hcard' : (translateDomain (-a) S).card = n ^ 2 := by simpa using hcard
  obtain ⟨b, hb⟩ := exists_square_symmDiff_sq_bound hn hcard'
    (translateDomain_neg_subset_rectangle ha)
  have htranslated :
      translateDomain a (translateDomain (-a) S ∆ translatedSquare n b) =
        S ∆ translatedSquare n (a + b) := by
    rw [translateDomain_symmDiff, translateDomain_square, translateDomain_add, add_neg_cancel]
    simp only [show (0 : Vertex) = (0, 0) from rfl, translateDomain_zero]
  have hsame : (S ∆ translatedSquare n (a + b)).card =
      (translateDomain (-a) S ∆ translatedSquare n b).card := by
    rw [← htranslated, card_translateDomain]
  refine ⟨a + b, ?_⟩
  simpa only [hsame] using hb

end SpanningTreeIsoperimetry
