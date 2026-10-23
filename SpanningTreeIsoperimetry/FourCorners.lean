module

public import SpanningTreeIsoperimetry.ProjectionEquality

@[expose] public section

/-!
# Geometry of convex lattice domains

All arguments in this module use the current project's actual finite lattice
sets and induced graph definitions. No imported manuscript theorem is used.

`vacancy_component_infinite` proves the absence of finite nearest-neighbor
holes. `four_corner_ferrers_partition` proves the geometric part of
`lem:four-corner`: a connected, row- and column-convex domain on its standard
minimal hull has four disjoint corner-anchored Ferrers defects. The arithmetic
short-side deficit bound is proved independently in `HullArithmetic.lean`.
-/

namespace SpanningTreeIsoperimetry

/-- The nearest-neighbor graph on the complement of the occupied domain. -/
def vacancyGraph (S : Domain) : SimpleGraph {v : Vertex // v ∉ S} :=
  lattice.comap Subtype.val

/-- A vacancy in an interval row has an entire empty horizontal ray. -/
theorem vacancy_has_empty_horizontal_ray {S : Domain} (hrow : IsRowConvex S)
    {p : Vertex} (hp : p ∉ S) :
    (∀ x : ℤ, x ≤ p.1 → (x, p.2) ∉ S) ∨
      (∀ x : ℤ, p.1 ≤ x → (x, p.2) ∉ S) := by
  by_cases hleft : ∀ x : ℤ, x ≤ p.1 → (x, p.2) ∉ S
  · exact Or.inl hleft
  · right
    push Not at hleft
    obtain ⟨x, hxp, hx⟩ := hleft
    intro y hpy hy
    exact hp (hrow x p.1 y p.2 hx hy hxp hpy)

/-- Every vertex on an empty rightward ray is reachable in the vacancy graph. -/
theorem vacancy_ray_right_reachable {S : Domain} {p : Vertex}
    (hray : ∀ x : ℤ, p.1 ≤ x → (x, p.2) ∉ S) (k : ℕ) :
    (vacancyGraph S).Reachable
      ⟨p, by simpa using hray p.1 le_rfl⟩
      ⟨(p.1 + k, p.2), hray _ (by omega)⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    apply ih.trans
    apply SimpleGraph.Adj.reachable
    change lattice.Adj (p.1 + k, p.2) (p.1 + (k + 1 : ℕ), p.2)
    simp [lattice]

/-- Every vertex on an empty leftward ray is reachable in the vacancy graph. -/
theorem vacancy_ray_left_reachable {S : Domain} {p : Vertex}
    (hray : ∀ x : ℤ, x ≤ p.1 → (x, p.2) ∉ S) (k : ℕ) :
    (vacancyGraph S).Reachable
      ⟨p, by simpa using hray p.1 le_rfl⟩
      ⟨(p.1 - k, p.2), hray _ (by omega)⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    apply ih.trans
    apply SimpleGraph.Adj.reachable
    change lattice.Adj (p.1 - k, p.2) (p.1 - (k + 1 : ℕ), p.2)
    simp [lattice]

/-- Row convexity alone excludes every finite nearest-neighbor vacancy
component. The statement concerns the actual connected-component support. -/
theorem vacancy_component_infinite {S : Domain} (hrow : IsRowConvex S)
    (p : {v : Vertex // v ∉ S}) :
    ((vacancyGraph S).connectedComponentMk p).supp.Infinite := by
  rcases vacancy_has_empty_horizontal_ray hrow p.property with hleft | hright
  · let ray : ℕ → {v : Vertex // v ∉ S} := fun k =>
      ⟨(p.val.1 - k, p.val.2), hleft _ (by omega)⟩
    have hinj : Function.Injective ray := by
      intro k l h
      have hx := congrArg (fun v : {v : Vertex // v ∉ S} => v.val.1) h
      dsimp [ray] at hx
      omega
    apply Set.infinite_of_injective_forall_mem hinj
    intro k
    apply (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
    exact (SimpleGraph.ConnectedComponent.sound (vacancy_ray_left_reachable hleft k)).symm
  · let ray : ℕ → {v : Vertex // v ∉ S} := fun k =>
      ⟨(p.val.1 + k, p.val.2), hright _ (by omega)⟩
    have hinj : Function.Injective ray := by
      intro k l h
      have hx := congrArg (fun v : {v : Vertex // v ∉ S} => v.val.1) h
      dsimp [ray] at hx
      omega
    apply Set.infinite_of_injective_forall_mem hinj
    intro k
    apply (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
    exact (SimpleGraph.ConnectedComponent.sound (vacancy_ray_right_reachable hright k)).symm

/-- A vertex property preserved along edges is preserved along every walk. -/
theorem walk_preserves_property {V : Type*} {G : SimpleGraph V} {P : V → Prop}
    (hstep : ∀ u v, G.Adj u v → P u → P v) {u v : V}
    (p : G.Walk u v) (hu : P u) : P v := by
  induction p with
  | nil => exact hu
  | cons hadj p ih => exact ih (hstep _ _ hadj hu)

/-- Two empty coordinate half-axes separate the lower-left quadrant from any
connected set meeting the opposite side. This is a finite graph cut argument. -/
theorem connected_quadrant_barrier {V : Type*} {G : SimpleGraph V}
    (hconn : G.Connected) (f g : V → ℤ)
    (hf : ∀ u v, G.Adj u v → f v ≤ f u + 1)
    (hg : ∀ u v, G.Adj u v → g v ≤ g u + 1)
    (haxisx : ∀ v, f v = 0 → g v ≤ 0 → False)
    (haxisy : ∀ v, g v = 0 → f v ≤ 0 → False)
    (houtside : ∃ v, 0 < f v ∨ 0 < g v) :
    ∀ v, ¬(f v ≤ 0 ∧ g v ≤ 0) := by
  intro v hv
  have hvstrict : f v < 0 ∧ g v < 0 := by
    constructor
    · have hne : f v ≠ 0 := fun h => haxisx v h hv.2
      omega
    · have hne : g v ≠ 0 := fun h => haxisy v h hv.1
      omega
  have hclosed : ∀ u w, G.Adj u w → (f u < 0 ∧ g u < 0) →
      f w < 0 ∧ g w < 0 := by
    intro u w hadj hu
    have hfw := hf u w hadj
    have hgw := hg u w hadj
    have hfw0 : f w ≤ 0 := by omega
    have hgw0 : g w ≤ 0 := by omega
    have hfn : f w ≠ 0 := fun h => haxisx w h hgw0
    have hgn : g w ≠ 0 := fun h => haxisy w h hfw0
    omega
  obtain ⟨w, hw⟩ := houtside
  obtain ⟨p⟩ := hconn v w
  have hwstrict := walk_preserves_property hclosed p hvstrict
  omega

/-- A vacancy with occupied points to its right and above has no occupied
point anywhere in its closed southwest quadrant. -/
theorem southwest_quadrant_empty {S : Domain} (hconn : (domainGraph S).Connected)
    (hrow : IsRowConvex S) (hcol : IsColumnConvex S)
    {p : Vertex} (hp : p ∉ S)
    (hright : ∃ x, p.1 < x ∧ (x, p.2) ∈ S)
    (habove : ∃ y, p.2 < y ∧ (p.1, y) ∈ S) :
    ∀ v ∈ S, ¬(v.1 ≤ p.1 ∧ v.2 ≤ p.2) := by
  obtain ⟨x, hx, hxp⟩ := hright
  obtain ⟨y, hy, hpy⟩ := habove
  have hcut := connected_quadrant_barrier hconn
    (fun v : (S : Set Vertex) => v.val.1 - p.1)
    (fun v : (S : Set Vertex) => v.val.2 - p.2)
    (fun u v h => by
      have hh : v.val.1 ≤ u.val.1 + 1 := lattice_fst_step (show lattice.Adj u.val v.val from h)
      omega)
    (fun u v h => by
      have hh : v.val.2 ≤ u.val.2 + 1 := lattice_snd_step (show lattice.Adj u.val v.val from h)
      omega)
    (fun v hxv hyv => by
      apply hp
      have hvx : v.val.1 = p.1 := by omega
      exact hcol p.1 v.val.2 p.2 y (by simp [← hvx]) hpy (by omega) hy.le)
    (fun v hyv hxv => by
      apply hp
      have hvy : v.val.2 = p.2 := by omega
      exact hrow v.val.1 p.1 x p.2 (by simp [← hvy]) hxp (by omega) hx.le)
    ⟨⟨(x, p.2), hxp⟩, Or.inl (by dsimp; omega)⟩
  intro v hv hle
  exact hcut ⟨v, hv⟩ (by dsimp; omega)

/-- A coordinate directed away from the chosen corner. -/
def cornerDirection (positive : Bool) (z : ℤ) : ℤ := if positive then z else -z

@[simp] theorem cornerDirection_zero (b : Bool) : cornerDirection b 0 = 0 := by
  cases b <;> rfl

theorem cornerDirection_chain (b : Bool) (x y z : ℤ) :
    cornerDirection b (x - y) + cornerDirection b (y - z) =
      cornerDirection b (x - z) := by
  cases b <;> simp [cornerDirection]

/-- The closed quadrant toward the chosen corner contains no occupied point.
`(true,true)` is the southwest corner. -/
def CornerEmpty (S : Domain) (p : Vertex) (bx byFlag : Bool) : Prop :=
  ∀ v ∈ S, ¬(cornerDirection bx (v.1 - p.1) ≤ 0 ∧
    cornerDirection byFlag (v.2 - p.2) ≤ 0)

theorem cornerEmpty_not_mem {S : Domain} {p : Vertex} {bx byFlag : Bool}
    (h : CornerEmpty S p bx byFlag) : p ∉ S := by
  intro hp
  exact h p hp (by simp)

/-- The quadrant cut argument in all four orientations. -/
theorem cornerEmpty_of_witnesses {S : Domain} (hconn : (domainGraph S).Connected)
    (hrow : IsRowConvex S) (hcol : IsColumnConvex S)
    {p : Vertex} (hp : p ∉ S) (bx byFlag : Bool)
    {x y : ℤ} (hx : 0 < cornerDirection bx (x - p.1))
    (hy : 0 < cornerDirection byFlag (y - p.2))
    (hxp : (x, p.2) ∈ S) (hpy : (p.1, y) ∈ S) : CornerEmpty S p bx byFlag := by
  have hcut := connected_quadrant_barrier hconn
    (fun v : (S : Set Vertex) => cornerDirection bx (v.val.1 - p.1))
    (fun v : (S : Set Vertex) => cornerDirection byFlag (v.val.2 - p.2))
    (fun u v h => by
      have huv : lattice.Adj u.val v.val := h
      have h₁ := lattice_fst_step huv
      have h₂ := lattice_fst_step huv.symm
      cases bx <;> simp only [cornerDirection, Bool.false_eq_true, ↓reduceIte] <;> omega)
    (fun u v h => by
      have huv : lattice.Adj u.val v.val := h
      have h₁ := lattice_snd_step huv
      have h₂ := lattice_snd_step huv.symm
      cases byFlag <;> simp only [cornerDirection, Bool.false_eq_true, ↓reduceIte] <;> omega)
    (fun v hxv hyv => by
      have hvx : v.val.1 = p.1 := by
        cases bx <;> simp [cornerDirection] at hxv <;> omega
      have hvS : (p.1, v.val.2) ∈ S := by simp [← hvx]
      apply hp
      cases byFlag
      · simp only [cornerDirection, Bool.false_eq_true, ↓reduceIte] at hy hyv
        exact hcol p.1 y p.2 v.val.2 hpy hvS (by omega) (by omega)
      · simp only [cornerDirection, ↓reduceIte] at hy hyv
        exact hcol p.1 v.val.2 p.2 y hvS hpy (by omega) (by omega))
    (fun v hyv hxv => by
      have hvy : v.val.2 = p.2 := by
        cases byFlag <;> simp [cornerDirection] at hyv <;> omega
      have hvS : (v.val.1, p.2) ∈ S := by simp [← hvy]
      apply hp
      cases bx
      · simp only [cornerDirection, Bool.false_eq_true, ↓reduceIte] at hx hxv
        exact hrow x p.1 v.val.1 p.2 hxp hvS (by omega) (by omega)
      · simp only [cornerDirection, ↓reduceIte] at hx hxv
        exact hrow v.val.1 p.1 x p.2 hvS hxp (by omega) (by omega))
    ⟨⟨(x, p.2), hxp⟩, Or.inl hx⟩
  intro v hv
  exact hcut ⟨v, hv⟩

theorem vacancy_has_empty_corner {S : Domain} (hconn : (domainGraph S).Connected)
    (hrow : IsRowConvex S) (hcol : IsColumnConvex S)
    {p : Vertex} (hp : p ∉ S)
    (hrowOcc : ∃ x, (x, p.2) ∈ S) (hcolOcc : ∃ y, (p.1, y) ∈ S) :
    ∃ bx byFlag, CornerEmpty S p bx byFlag := by
  obtain ⟨x, hx⟩ := hrowOcc
  obtain ⟨y, hy⟩ := hcolOcc
  have hxne : x ≠ p.1 := by intro h; exact hp (by simpa [h] using hx)
  have hyne : y ≠ p.2 := by intro h; exact hp (by simpa [h] using hy)
  by_cases hxr : p.1 < x <;> by_cases hyu : p.2 < y
  · exact ⟨true, true, cornerEmpty_of_witnesses hconn hrow hcol hp true true
      (by simpa [cornerDirection] using hxr) (by simpa [cornerDirection] using hyu) hx hy⟩
  · exact ⟨true, false, cornerEmpty_of_witnesses hconn hrow hcol hp true false
      (by simpa [cornerDirection] using hxr) (by simp [cornerDirection]; omega) hx hy⟩
  · exact ⟨false, true, cornerEmpty_of_witnesses hconn hrow hcol hp false true
      (by simp [cornerDirection]; omega) (by simpa [cornerDirection] using hyu) hx hy⟩
  · exact ⟨false, false, cornerEmpty_of_witnesses hconn hrow hcol hp false false
      (by simp [cornerDirection]; omega) (by simp [cornerDirection]; omega) hx hy⟩

theorem cornerDirection_unique {z : ℤ} {b c : Bool}
    (hb : 0 < cornerDirection b z) (hc : 0 < cornerDirection c z) : b = c := by
  cases b <;> cases c <;> simp_all [cornerDirection] <;> omega

theorem cornerEmpty_unique {S : Domain} {p : Vertex} {bx byFlag cx cy : Bool}
    (hrowOcc : ∃ x, (x, p.2) ∈ S) (hcolOcc : ∃ y, (p.1, y) ∈ S)
    (h₁ : CornerEmpty S p bx byFlag) (h₂ : CornerEmpty S p cx cy) :
    bx = cx ∧ byFlag = cy := by
  obtain ⟨x, hx⟩ := hrowOcc
  obtain ⟨y, hy⟩ := hcolOcc
  have hx₁ := h₁ (x, p.2) hx
  have hx₂ := h₂ (x, p.2) hx
  have hy₁ := h₁ (p.1, y) hy
  have hy₂ := h₂ (p.1, y) hy
  simp only [sub_self, cornerDirection_zero, le_refl, and_true, true_and, not_le] at hx₁ hx₂ hy₁ hy₂
  exact ⟨cornerDirection_unique hx₁ hx₂, cornerDirection_unique hy₁ hy₂⟩

/-- Quadrant emptiness is closed under movement toward its corner. -/
theorem cornerEmpty_lower_closed {S : Domain} {p q : Vertex} {bx byFlag : Bool}
    (hp : CornerEmpty S p bx byFlag)
    (hx : cornerDirection bx (q.1 - p.1) ≤ 0)
    (hy : cornerDirection byFlag (q.2 - p.2) ≤ 0) : CornerEmpty S q bx byFlag := by
  intro v hv hle
  apply hp v hv
  have hchainx := cornerDirection_chain bx v.1 q.1 p.1
  have hchainy := cornerDirection_chain byFlag v.2 q.2 p.2
  constructor <;> omega

/-- The usual minimal origin-based rectangle, expressed through its four
attained sides. -/
structure IsStandardHull (S : Domain) (r s : ℕ) : Prop where
  subset : S ⊆ rectangle r s
  left : ∃ y, (0, y) ∈ S
  right : ∃ y, ((r : ℤ) - 1, y) ∈ S
  bottom : ∃ x, (x, 0) ∈ S
  top : ∃ x, (x, (s : ℤ) - 1) ∈ S

theorem IsStandardHull.row_occupied {S : Domain} {r s : ℕ}
    (hull : IsStandardHull S r s) (hconn : (domainGraph S).Connected)
    {y : ℤ} (hy0 : 0 ≤ y) (hys : y < s) : ∃ x, (x, y) ∈ S := by
  obtain ⟨xb, hxb⟩ := hull.bottom
  obtain ⟨xt, hxt⟩ := hull.top
  have h0 : (0 : ℤ) ∈ S.image Prod.snd := Finset.mem_image.mpr ⟨(xb, 0), hxb, rfl⟩
  have hs : (s : ℤ) - 1 ∈ S.image Prod.snd :=
    Finset.mem_image.mpr ⟨(xt, (s : ℤ) - 1), hxt, rfl⟩
  have hy := connected_yProjection_interval hconn 0 h0 ((s : ℤ) - 1) hs y hy0 (by omega)
  obtain ⟨v, hv, hvy⟩ := Finset.mem_image.mp hy
  exact ⟨v.1, by simpa [← hvy] using hv⟩

theorem IsStandardHull.column_occupied {S : Domain} {r s : ℕ}
    (hull : IsStandardHull S r s) (hconn : (domainGraph S).Connected)
    {x : ℤ} (hx0 : 0 ≤ x) (hxr : x < r) : ∃ y, (x, y) ∈ S := by
  obtain ⟨yl, hyl⟩ := hull.left
  obtain ⟨yr, hyr⟩ := hull.right
  have h0 : (0 : ℤ) ∈ S.image Prod.fst := Finset.mem_image.mpr ⟨(0, yl), hyl, rfl⟩
  have hr : (r : ℤ) - 1 ∈ S.image Prod.fst :=
    Finset.mem_image.mpr ⟨((r : ℤ) - 1, yr), hyr, rfl⟩
  have hx := connected_xProjection_interval hconn 0 h0 ((r : ℤ) - 1) hr x hx0 (by omega)
  obtain ⟨v, hv, hvx⟩ := Finset.mem_image.mp hx
  exact ⟨v.2, by simpa [← hvx] using hv⟩

noncomputable def cornerVacancies (S : Domain) (r s : ℕ) (bx byFlag : Bool) : Domain := by
  classical
  exact (rectangle r s).filter (fun p => CornerEmpty S p bx byFlag)

@[simp] theorem mem_cornerVacancies {S : Domain} {r s : ℕ} {bx byFlag : Bool} {p : Vertex} :
    p ∈ cornerVacancies S r s bx byFlag ↔ p ∈ rectangle r s ∧ CornerEmpty S p bx byFlag := by
  classical
  exact Finset.mem_filter

/-- Every hull vacancy belongs to exactly one of the four corner ideals. -/
theorem four_corner_partition {S : Domain} {r s : ℕ}
    (hull : IsStandardHull S r s) (hconn : (domainGraph S).Connected)
    (hrow : IsRowConvex S) (hcol : IsColumnConvex S) (p : Vertex) :
    p ∈ rectangle r s \ S ↔ ∃! c : Bool × Bool,
      p ∈ cornerVacancies S r s c.1 c.2 := by
  constructor
  · intro hp
    obtain ⟨hR, hvac⟩ := Finset.mem_sdiff.mp hp
    have hb := mem_rectangle.mp hR
    have hro := hull.row_occupied hconn hb.2.2.1 hb.2.2.2
    have hco := hull.column_occupied hconn hb.1 hb.2.1
    obtain ⟨bx, byFlag, hc⟩ := vacancy_has_empty_corner hconn hrow hcol hvac hro hco
    refine ⟨(bx, byFlag), mem_cornerVacancies.mpr ⟨hR, hc⟩, ?_⟩
    intro c hc'
    have heq := cornerEmpty_unique hro hco (mem_cornerVacancies.mp hc').2 hc
    exact Prod.ext heq.1 heq.2
  · rintro ⟨c, hc, _⟩
    have hm := mem_cornerVacancies.mp hc
    exact Finset.mem_sdiff.mpr ⟨hm.1, cornerEmpty_not_mem hm.2⟩

/-- Each corner piece has the Ferrers lower-ideal property in coordinates
directed away from that corner. -/
theorem cornerVacancies_lower_closed {S : Domain} {r s : ℕ} {bx byFlag : Bool}
    {p q : Vertex} (hp : p ∈ cornerVacancies S r s bx byFlag)
    (hq : q ∈ rectangle r s)
    (hx : cornerDirection bx (q.1 - p.1) ≤ 0)
    (hy : cornerDirection byFlag (q.2 - p.2) ≤ 0) :
    q ∈ cornerVacancies S r s bx byFlag :=
  mem_cornerVacancies.mpr ⟨hq, cornerEmpty_lower_closed (mem_cornerVacancies.mp hp).2 hx hy⟩

/-- Natural coordinates based at one of the four rectangle corners. -/
def cornerEmbedding (r s : ℕ) (bx byFlag : Bool) (q : ℕ × ℕ) : Vertex :=
  (if bx then q.1 else (r : ℤ) - 1 - q.1,
   if byFlag then q.2 else (s : ℤ) - 1 - q.2)

theorem cornerEmbedding_injective (r s : ℕ) (bx byFlag : Bool) :
    Function.Injective (cornerEmbedding r s bx byFlag) := by
  intro p q heq
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  apply Prod.ext
  · cases bx <;> simp only [cornerEmbedding, Bool.false_eq_true, ↓reduceIte] at hx <;> omega
  · cases byFlag <;> simp only [cornerEmbedding, Bool.false_eq_true, ↓reduceIte] at hy <;> omega

theorem cornerEmbedding_mem_rectangle {r s : ℕ} (bx byFlag : Bool) {q : ℕ × ℕ}
    (hx : q.1 < r) (hy : q.2 < s) : cornerEmbedding r s bx byFlag q ∈ rectangle r s := by
  have hx' : (q.1 : ℤ) < r := by exact_mod_cast hx
  have hy' : (q.2 : ℤ) < s := by exact_mod_cast hy
  cases bx <;> cases byFlag <;> simp only [cornerEmbedding, mem_rectangle,
    Bool.false_eq_true, ↓reduceIte] <;> omega

theorem cornerEmbedding_direction_fst (r s : ℕ) (bx byFlag : Bool) (p q : ℕ × ℕ) :
    cornerDirection bx ((cornerEmbedding r s bx byFlag q).1 -
      (cornerEmbedding r s bx byFlag p).1) = (q.1 : ℤ) - p.1 := by
  cases bx <;> simp [cornerEmbedding, cornerDirection]

theorem cornerEmbedding_direction_snd (r s : ℕ) (bx byFlag : Bool) (p q : ℕ × ℕ) :
    cornerDirection byFlag ((cornerEmbedding r s bx byFlag q).2 -
      (cornerEmbedding r s bx byFlag p).2) = (q.2 : ℤ) - p.2 := by
  cases byFlag <;> simp [cornerEmbedding, cornerDirection]

/-- The actual corner defect, expressed as a finite subset of `ℕ × ℕ`. -/
noncomputable def cornerDiagram (S : Domain) (r s : ℕ) (bx byFlag : Bool) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.range r ×ˢ Finset.range s).filter
    (fun q => cornerEmbedding r s bx byFlag q ∈ cornerVacancies S r s bx byFlag)

/-- All four corner diagrams satisfy the project's actual `IsFerrers`
definition, not merely a surrogate shape predicate. -/
theorem cornerDiagram_isFerrers (S : Domain) (r s : ℕ) (bx byFlag : Bool) :
    IsFerrers (cornerDiagram S r s bx byFlag) := by
  classical
  intro p hp q hx hy
  have hp' := Finset.mem_filter.mp hp
  have hpbox := Finset.mem_product.mp hp'.1
  have hpx := Finset.mem_range.mp hpbox.1
  have hpy := Finset.mem_range.mp hpbox.2
  have hqx : q.1 < r := lt_of_le_of_lt hx hpx
  have hqy : q.2 < s := lt_of_le_of_lt hy hpy
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hqx, Finset.mem_range.mpr hqy⟩, ?_⟩
  apply cornerVacancies_lower_closed hp'.2 (cornerEmbedding_mem_rectangle bx byFlag hqx hqy)
  · rw [cornerEmbedding_direction_fst]
    exact sub_nonpos.mpr (by exact_mod_cast hx)
  · rw [cornerEmbedding_direction_snd]
    exact sub_nonpos.mpr (by exact_mod_cast hy)

theorem corner_coordinate_preimage {r : ℕ} (b : Bool) {z : ℤ}
    (hz0 : 0 ≤ z) (hzr : z < r) :
    ∃ i : ℕ, i < r ∧ (if b then (i : ℤ) else (r : ℤ) - 1 - i) = z := by
  cases b
  · have hz : 0 ≤ (r : ℤ) - 1 - z := by omega
    have hc := Int.toNat_of_nonneg hz
    refine ⟨((r : ℤ) - 1 - z).toNat, ?_, ?_⟩
    · omega
    · simp only [Bool.false_eq_true, ↓reduceIte, hc]
      omega
  · have hc := Int.toNat_of_nonneg hz0
    refine ⟨z.toNat, ?_, ?_⟩
    · omega
    · simpa using hc

theorem cornerEmbedding_surjective_on_rectangle {r s : ℕ} (bx byFlag : Bool)
    {v : Vertex} (hv : v ∈ rectangle r s) :
    ∃ q ∈ Finset.range r ×ˢ Finset.range s, cornerEmbedding r s bx byFlag q = v := by
  have hb := mem_rectangle.mp hv
  obtain ⟨i, hi, hix⟩ := corner_coordinate_preimage bx hb.1 hb.2.1
  obtain ⟨j, hj, hjy⟩ := corner_coordinate_preimage byFlag hb.2.2.1 hb.2.2.2
  exact ⟨(i,j), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hj⟩,
    Prod.ext hix hjy⟩

/-- The natural-coordinate diagram maps exactly onto the physical corner
vacancies; the embedding is a translation and coordinate reflection. -/
theorem cornerDiagram_image (S : Domain) (r s : ℕ) (bx byFlag : Bool) :
    (cornerDiagram S r s bx byFlag).image (cornerEmbedding r s bx byFlag) =
      cornerVacancies S r s bx byFlag := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hq).2
  · intro hv
    obtain ⟨q, hq, heq⟩ := cornerEmbedding_surjective_on_rectangle bx byFlag
      (mem_cornerVacancies.mp hv).1
    refine Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, ?_⟩, heq⟩
    simpa only [heq] using hv

/-- The four-corner decomposition in the manuscript: every vacancy belongs
to exactly one reflected, corner-anchored Ferrers diagram. -/
theorem four_corner_ferrers_partition {S : Domain} {r s : ℕ}
    (hull : IsStandardHull S r s) (hconn : (domainGraph S).Connected)
    (hrow : IsRowConvex S) (hcol : IsColumnConvex S) (p : Vertex) :
    (∀ bx byFlag, IsFerrers (cornerDiagram S r s bx byFlag)) ∧
    (p ∈ rectangle r s \ S ↔ ∃! c : Bool × Bool,
      p ∈ (cornerDiagram S r s c.1 c.2).image (cornerEmbedding r s c.1 c.2)) := by
  refine ⟨cornerDiagram_isFerrers S r s, ?_⟩
  simp only [cornerDiagram_image]
  exact four_corner_partition hull hconn hrow hcol p

end SpanningTreeIsoperimetry
