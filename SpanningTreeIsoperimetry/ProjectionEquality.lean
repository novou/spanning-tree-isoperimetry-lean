module

public import SpanningTreeIsoperimetry.Projection

@[expose] public section

/-!
# Equality in the edge projection bound

An occupied row has exactly one terminal vertex precisely when it is an
integer interval. The terminal-vertex bijection characterizes equality in
both directional edge bounds, hence in their sum for the actual graph.
-/

namespace SpanningTreeIsoperimetry

/-- Vertices at the right end of a horizontal run. -/
def horizontalTerminals (S : Domain) : Domain := S.filter (fun v => east v ∉ S)

theorem row_has_terminal {S : Domain} {v : Vertex} (hv : v ∈ S) :
    ∃ w ∈ horizontalTerminals S, w.2 = v.2 ∧ v.1 ≤ w.1 := by
  let row := S.filter (fun w => w.2 = v.2)
  have hrow : row.Nonempty := ⟨v, by simp [row, hv]⟩
  obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image row Prod.fst hrow
  have hwS := (Finset.mem_filter.mp hw).1
  have hwy := (Finset.mem_filter.mp hw).2
  have hend : east w ∉ S := by
    intro he
    have herow : east w ∈ row := Finset.mem_filter.mpr ⟨he, hwy⟩
    have hh := hmax (east w) herow
    change w.1 + 1 ≤ w.1 at hh
    omega
  exact ⟨w, Finset.mem_filter.mpr ⟨hwS, hend⟩, hwy,
    hmax v (by simp [row, hv])⟩

theorem horizontalTerminals_image (S : Domain) :
    (horizontalTerminals S).image Prod.snd = S.image Prod.snd := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨v, (Finset.mem_filter.mp hv).1, rfl⟩
  · intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w, hw, hwy, _⟩ := row_has_terminal hv
    exact Finset.mem_image.mpr ⟨w, hw, hwy⟩

theorem horizontalTerminals_injective_iff (S : Domain) :
    Set.InjOn Prod.snd (horizontalTerminals S : Set Vertex) ↔ IsRowConvex S := by
  constructor
  · intro hinj a x b y ha hb hax hxb
    by_contra hx
    have halt : a < x := by
      by_contra hn
      have : a = x := by omega
      exact hx (this ▸ ha)
    let left := S.filter (fun v => v.2 = y ∧ v.1 < x)
    have hleft : left.Nonempty := ⟨(a,y), by simp [left, ha, halt]⟩
    obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image left Prod.fst hleft
    have hwS := (Finset.mem_filter.mp hw).1
    have hwy := (Finset.mem_filter.mp hw).2.1
    have hwx := (Finset.mem_filter.mp hw).2.2
    have hwterminal : w ∈ horizontalTerminals S := by
      refine Finset.mem_filter.mpr ⟨hwS, ?_⟩
      intro he
      have hne : w.1 + 1 ≠ x := by
        intro heq
        apply hx
        simpa [east, heq, hwy] using he
      have hlt : w.1 + 1 < x := by omega
      have hele : east w ∈ left := Finset.mem_filter.mpr ⟨he, hwy, hlt⟩
      have hh := hmax (east w) hele
      change w.1 + 1 ≤ w.1 at hh
      omega
    obtain ⟨z, hz, hzy, hbz⟩ := row_has_terminal hb
    have heq : w = z := hinj hwterminal hz (hwy.trans hzy.symm)
    have hbwx : b ≤ w.1 := by simpa only [heq] using hbz
    omega
  · intro hconv a ha b hb hab
    have haS := (Finset.mem_filter.mp ha).1
    have hbS := (Finset.mem_filter.mp hb).1
    have haend := (Finset.mem_filter.mp ha).2
    have hbend := (Finset.mem_filter.mp hb).2
    apply Prod.ext
    · apply le_antisymm
      · by_contra hn
        have hba : b.1 + 1 ≤ a.1 := by omega
        apply hbend
        change (b.1 + 1, b.2) ∈ S
        exact hconv b.1 (b.1 + 1) a.1 b.2 hbS
          (by simpa only [← hab] using haS) (by omega) hba
      · by_contra hn
        have hab' : a.1 + 1 ≤ b.1 := by omega
        apply haend
        change (a.1 + 1, a.2) ∈ S
        exact hconv a.1 (a.1 + 1) b.1 a.2 haS
          (by simpa [hab] using hbS) (by omega) hab'
    · exact hab

theorem horizontal_count_add_rows_eq_iff (S : Domain) :
    (horizontalSources S).card + (S.image Prod.snd).card = S.card ↔ IsRowConvex S := by
  have hp := Finset.card_filter_add_card_filter_not (s := S) (fun v => east v ∈ S)
  change (horizontalSources S).card + (horizontalTerminals S).card = S.card at hp
  rw [← horizontalTerminals_injective_iff, ← Finset.card_image_iff,
    horizontalTerminals_image]
  omega

theorem horizontalSources_transpose (S : Domain) :
    horizontalSources (transposeDomain S) = transposeDomain (verticalSources S) := by
  ext v
  rcases v with ⟨x,y⟩
  simp only [horizontalSources, Finset.mem_filter, mem_transposeDomain]
  change (y,x) ∈ S ∧ (y,x+1) ∈ S ↔ (y,x) ∈ verticalSources S
  exact (Finset.mem_filter (s := S) (a := (y,x)) (p := fun v => north v ∈ S)).symm

theorem image_snd_transpose (S : Domain) :
    (transposeDomain S).image Prod.snd = S.image Prod.fst := by
  rw [transposeDomain, Finset.image_image]
  rfl

theorem rowConvex_transpose_iff (S : Domain) :
    IsRowConvex (transposeDomain S) ↔ IsColumnConvex S := by
  constructor
  · intro h x y₁ y y₂ h₁ h₂ hl hu
    have hh := h y₁ y y₂ x (mem_transposeDomain.mpr h₁)
      (mem_transposeDomain.mpr h₂) hl hu
    exact mem_transposeDomain.mp hh
  · intro h x₁ x x₂ y h₁ h₂ hl hu
    exact mem_transposeDomain.mpr
      (h y x₁ x x₂ (mem_transposeDomain.mp h₁) (mem_transposeDomain.mp h₂) hl hu)

theorem vertical_count_add_columns_eq_iff (S : Domain) :
    (verticalSources S).card + (S.image Prod.fst).card = S.card ↔ IsColumnConvex S := by
  have h := horizontal_count_add_rows_eq_iff (transposeDomain S)
  simpa only [horizontalSources_transpose, card_transposeDomain, image_snd_transpose,
    rowConvex_transpose_iff] using h

/-- Equality in the strong projection bound is exactly convexity of all rows
and all columns. No connectedness assumption is required for this equivalence. -/
theorem edgeCount_add_projections_eq_iff (S : Domain) :
    Nat.card (domainGraph S).edgeSet +
      (S.image Prod.fst).card + (S.image Prod.snd).card = 2 * S.card ↔
    IsRowConvex S ∧ IsColumnConvex S := by
  have hH := horizontal_count_add_rows_le S
  have hV := vertical_count_add_columns_le S
  rw [edgeCount_eq_forward_count, ← horizontal_count_add_rows_eq_iff,
    ← vertical_count_add_columns_eq_iff]
  omega

/-- A walk whose integer coordinate increases by at most one per edge meets
every integer between its endpoint coordinates. -/
theorem walk_integer_intermediate {V : Type*} {G : SimpleGraph V} (f : V → ℤ)
    (hstep : ∀ u v, G.Adj u v → f v ≤ f u + 1)
    {u v : V} (p : G.Walk u v) {k : ℤ} (hu : f u ≤ k) (hv : k ≤ f v) :
    ∃ w : V, f w = k := by
  induction p with
  | @nil u => exact ⟨u, by omega⟩
  | @cons u w v h p ih =>
    by_cases hw : f w ≤ k
    · exact ih hw hv
    · exact ⟨u, by have hh := hstep u w h; omega⟩

/-- Integer interval property of a finite set. -/
def IsIntegerInterval (T : Finset ℤ) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, ∀ x : ℤ, a ≤ x → x ≤ b → x ∈ T

theorem connected_image_interval {S : Domain} (hconn : (domainGraph S).Connected)
    (f : Vertex → ℤ) (hstep : ∀ u v, lattice.Adj u v → f v ≤ f u + 1) :
    IsIntegerInterval (S.image f) := by
  intro a ha b hb x hax hxb
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨p⟩ := hconn (⟨u,hu⟩ : (S : Set Vertex)) ⟨v,hv⟩
  obtain ⟨w, hw⟩ := walk_integer_intermediate
    (fun w : (S : Set Vertex) => f w.val)
    (fun u v h => hstep u.val v.val h) p hax hxb
  exact Finset.mem_image.mpr ⟨w.val, w.property, hw⟩

theorem lattice_fst_step {u v : Vertex} (h : lattice.Adj u v) : v.1 ≤ u.1 + 1 := by
  rcases h with ⟨hx,hy⟩ | ⟨hy,hx⟩
  · omega
  · have hh := eq_or_eq_neg_of_abs_eq hx
    omega

theorem lattice_snd_step {u v : Vertex} (h : lattice.Adj u v) : v.2 ≤ u.2 + 1 := by
  rcases h with ⟨hx,hy⟩ | ⟨hy,hx⟩
  · have hh := eq_or_eq_neg_of_abs_eq hy
    omega
  · omega

theorem connected_xProjection_interval {S : Domain} (hconn : (domainGraph S).Connected) :
    IsIntegerInterval (S.image Prod.fst) :=
  connected_image_interval hconn Prod.fst (fun _ _ h => lattice_fst_step h)

theorem connected_yProjection_interval {S : Domain} (hconn : (domainGraph S).Connected) :
    IsIntegerInterval (S.image Prod.snd) :=
  connected_image_interval hconn Prod.snd (fun _ _ h => lattice_snd_step h)

theorem integerInterval_eq_Icc {T : Finset ℤ} (hT : T.Nonempty)
    (hinterval : IsIntegerInterval T) : T = Finset.Icc (T.min' hT) (T.max' hT) := by
  ext x
  constructor
  · intro hx
    exact Finset.mem_Icc.mpr ⟨T.min'_le x hx, T.le_max' x hx⟩
  · intro hx
    exact hinterval _ (T.min'_mem hT) _ (T.max'_mem hT) x
      (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hx).2

theorem integerInterval_card {T : Finset ℤ} (hT : T.Nonempty)
    (hinterval : IsIntegerInterval T) :
    T.card = (T.max' hT + 1 - T.min' hT).toNat := by
  calc
    T.card = (Finset.Icc (T.min' hT) (T.max' hT)).card :=
      congrArg Finset.card (integerInterval_eq_Icc hT hinterval)
    _ = _ := by rw [Int.card_Icc]

/-- Number of lattice columns in the smallest axis-aligned rectangular hull. -/
def hullWidth (S : Domain) (hS : S.Nonempty) : ℕ :=
  ((S.image Prod.fst).max' (hS.image Prod.fst) + 1 -
    (S.image Prod.fst).min' (hS.image Prod.fst)).toNat

/-- Number of lattice rows in the smallest axis-aligned rectangular hull. -/
def hullHeight (S : Domain) (hS : S.Nonempty) : ℕ :=
  ((S.image Prod.snd).max' (hS.image Prod.snd) + 1 -
    (S.image Prod.snd).min' (hS.image Prod.snd)).toNat

theorem connected_domain_nonempty {S : Domain} (hconn : (domainGraph S).Connected) :
    S.Nonempty := by
  obtain ⟨v⟩ := hconn.nonempty
  exact ⟨v.val, v.property⟩

theorem connected_xProjection_card {S : Domain} (hconn : (domainGraph S).Connected)
    (hS : S.Nonempty) : (S.image Prod.fst).card = hullWidth S hS :=
  integerInterval_card (hS.image Prod.fst) (connected_xProjection_interval hconn)

theorem connected_yProjection_card {S : Domain} (hconn : (domainGraph S).Connected)
    (hS : S.Nonempty) : (S.image Prod.snd).card = hullHeight S hS :=
  integerInterval_card (hS.image Prod.snd) (connected_yProjection_interval hconn)

/-- Equality in the sharp edge bound is row and column convexity together
with the minimum possible sum of projection sizes. -/
theorem edgeCount_projection_eq_iff (S : Domain) (hS : S.Nonempty) :
    Nat.card (domainGraph S).edgeSet =
      2 * S.card - ⌈2 * Real.sqrt (S.card : ℝ)⌉₊ ↔
    IsRowConvex S ∧ IsColumnConvex S ∧
      (S.image Prod.fst).card + (S.image Prod.snd).card =
        ⌈2 * Real.sqrt (S.card : ℝ)⌉₊ := by
  have hside := minimum_side_sum_le
    (ceil_sqrt_is_minimum_side_sum (Finset.card_pos.mpr hS))
    (card_le_projection_product S)
  have hE := edgeCount_add_projections_le S
  have hx : (S.image Prod.fst).card ≤ S.card := Finset.card_image_le
  have hy : (S.image Prod.snd).card ≤ S.card := Finset.card_image_le
  constructor
  · intro heq
    have heq' : Nat.card (domainGraph S).edgeSet +
        (S.image Prod.fst).card + (S.image Prod.snd).card = 2 * S.card := by omega
    obtain ⟨hr,hc⟩ := (edgeCount_add_projections_eq_iff S).mp heq'
    exact ⟨hr,hc,by omega⟩
  · rintro ⟨hr,hc,hside'⟩
    have heq' := (edgeCount_add_projections_eq_iff S).mpr ⟨hr,hc⟩
    omega

/-- For a connected domain the projection sizes are the actual hull side
lengths. This is the equality characterization in manuscript `lem:projection-bound`. -/
theorem edgeCount_projection_eq_iff_hull {S : Domain}
    (hconn : (domainGraph S).Connected) (hS : S.Nonempty) :
    Nat.card (domainGraph S).edgeSet =
      2 * S.card - ⌈2 * Real.sqrt (S.card : ℝ)⌉₊ ↔
    IsRowConvex S ∧ IsColumnConvex S ∧
      hullWidth S hS + hullHeight S hS = ⌈2 * Real.sqrt (S.card : ℝ)⌉₊ := by
  rw [edgeCount_projection_eq_iff S hS,
    connected_xProjection_card hconn hS, connected_yProjection_card hconn hS]

end SpanningTreeIsoperimetry
