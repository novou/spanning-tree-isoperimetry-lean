import SpanningTreeIsoperimetry.PolarizationDeterminant
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Strict polarization

Actual finite matrix powers are expanded into products along vertex sequences.
A path in the polarized preferred half-plane, connecting opposite singleton
orbits, supplies a negative closed-walk term in the transformed matrix. This
proves strictness for some even moment and for every determinant parameter
z ≥ 4, with the manuscript's actual geometric hypotheses.
-/

namespace SpanningTreeIsoperimetry.Polarization

open scoped BigOperators

/-- Weight of a path with `n` prescribed intermediate vertices. -/
def chainWeight {I : Type*} (A : Matrix I I ℝ) :
    (n : ℕ) → (Fin n → I) → I → I → ℝ
  | 0, _, i, j => A i j
  | n + 1, v, i, j => A i (v 0) * chainWeight A n (Fin.tail v) (v 0) j

theorem pow_eq_sum_chainWeight {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (n : ℕ) (i j : I) :
    (A ^ (n + 1)) i j = ∑ v : Fin n → I, chainWeight A n v i j := by
  induction n generalizing i j with
  | zero => simp [chainWeight]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih, Finset.mul_sum]
    rw [← Fintype.sum_prod_type (fun p : I × (Fin n → I) => A i p.1 * chainWeight A n p.2 p.1 j)]
    have he := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => I))
      (fun v => chainWeight A (n + 1) v i j)
    simpa only [Fin.consEquiv, Equiv.coe_fn_mk, chainWeight, Fin.cons_zero,
      Fin.tail_cons] using he

def absoluteMatrix {I : Type*} (A : Matrix I I ℝ) : Matrix I I ℝ :=
  fun i j => |A i j|

theorem chainWeight_absolute {I : Type*} (A : Matrix I I ℝ)
    (n : ℕ) (v : Fin n → I) (i j : I) :
    chainWeight (absoluteMatrix A) n v i j = |chainWeight A n v i j| := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih => simp only [chainWeight, ih, absoluteMatrix, abs_mul]

theorem matrix_power_strict_of_negative_chain {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (n : ℕ) (v : Fin n → I) (i j : I)
    (hneg : chainWeight A n v i j < 0) :
    (A ^ (n + 1)) i j < (absoluteMatrix A ^ (n + 1)) i j := by
  rw [pow_eq_sum_chainWeight, pow_eq_sum_chainWeight]
  apply Finset.sum_lt_sum
  · intro w _
    rw [chainWeight_absolute]
    exact le_abs_self _
  · refine ⟨v, Finset.mem_univ _, ?_⟩
    rw [chainWeight_absolute, abs_of_neg hneg]
    linarith

/-- One negative closed-walk summand makes a positive-length trace comparison strict. -/
theorem matrix_trace_strict_of_negative_chain {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (n : ℕ) (v : Fin n → I) (i : I)
    (hneg : chainWeight A n v i i < 0) :
    Matrix.trace (A ^ (n + 1)) < Matrix.trace (absoluteMatrix A ^ (n + 1)) := by
  apply Finset.sum_lt_sum
  · intro j _
    exact (le_abs_self _).trans (matrix_abs_pow_le A (absoluteMatrix A) (fun _ _ => le_rfl) _ j j)
  · exact ⟨i, Finset.mem_univ _, matrix_power_strict_of_negative_chain A n v i i hneg⟩

/-- Multiplicative weight of a list of successive arrivals. -/
def travelWeight {I : Type*} (A : Matrix I I ℝ) (i : I) : List I → ℝ
  | [] => 1
  | j :: l => A i j * travelWeight A j l

theorem travelWeight_append {I : Type*} (A : Matrix I I ℝ) (i : I) (l r : List I) :
    travelWeight A i (l ++ r) = travelWeight A i l * travelWeight A (l.getLastD i) r := by
  induction l generalizing i with
  | nil => simp [travelWeight]
  | cons j l ih =>
    simp only [List.cons_append, travelWeight, ih]
    rw [List.getLastD_cons]
    ring

theorem chainWeight_eq_travelWeight {I : Type*} (A : Matrix I I ℝ)
    (n : ℕ) (v : Fin n → I) (i j : I) :
    chainWeight A n v i j = travelWeight A i (List.ofFn v ++ [j]) := by
  induction n generalizing i j with
  | zero => simp [chainWeight, travelWeight]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [List.cons_append, travelWeight, chainWeight, ih]
    rw [show Fin.tail v = (fun i : Fin n => v i.succ) from rfl]

theorem matrix_trace_strict_of_negative_loop {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (i : I) (middle : List I)
    (hneg : travelWeight A i (middle ++ [i]) < 0) :
    Matrix.trace (A ^ (middle.length + 1)) <
      Matrix.trace (absoluteMatrix A ^ (middle.length + 1)) := by
  apply matrix_trace_strict_of_negative_chain A middle.length middle.get i
  rw [chainWeight_eq_travelWeight, List.ofFn_get]
  exact hneg

def pathLayer {I : Type*} : Bool → I → I ⊕ I
  | true, i => Sum.inl i
  | false, i => Sum.inr i

theorem lifted_path_weight {I J : Type*} (A : Matrix (I ⊕ I) (I ⊕ I) ℝ)
    (f : J → I) (R : J → J → Prop) (c d : J → ℝ)
    (hedge : ∀ x y, R x y → ∀ s t,
      A (pathLayer s (f x)) (pathLayer t (f y)) = if s = t then c y else d y)
    (a b : J) (middle : List J) (hpath : (a :: middle ++ [b]).IsChain R) (s t : Bool) :
    travelWeight A (pathLayer s (f a))
        (middle.map (fun x => pathLayer s (f x)) ++ [pathLayer t (f b)]) =
      (middle.map c).prod * (if s = t then c b else d b) := by
  induction middle generalizing a with
  | nil =>
    have hab : R a b := (List.isChain_cons_cons.mp hpath).1
    simp [travelWeight, hedge a b hab s t]
  | cons x middle ih =>
    have hab := (List.isChain_cons_cons.mp hpath).1
    have hrest := (List.isChain_cons_cons.mp hpath).2
    simp only [List.map_cons, List.cons_append, travelWeight, hedge a x hab s s,
      ite_true, ih x hrest, List.prod_cons]
    ring

theorem reverse_chain_ends {J : Type*} (R : J → J → Prop) (hsym : ∀ {x y}, R x y → R y x)
    (a b : J) (middle : List J) (hpath : (a :: middle ++ [b]).IsChain R) :
    (b :: middle.reverse ++ [a]).IsChain R := by
  have hrev := List.isChain_reverse.mpr (hpath.imp (fun _ _ h => hsym h))
  simpa only [List.reverse_cons, List.reverse_append, List.reverse_singleton, List.reverse_nil,
    List.cons_append, List.nil_append, List.append_assoc] using hrev

theorem getLastD_append_one {I : Type*} (l : List I) (last fallback : I) :
    (l ++ [last]).getLastD fallback = last := by
  induction l generalizing fallback with
  | nil => simp
  | cons x l ih => simp only [List.cons_append, List.getLastD_cons, ih]

theorem list_prod_map_pos {I : Type*} (c : I → ℝ) (l : List I)
    (hc : ∀ i ∈ l, 0 < c i) : 0 < (l.map c).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_pos (hc x (by simp)) (ih (fun i hi => hc i (by simp [hi])))

/-- An actual path with positive internal means and opposite endpoint differences
produces a negative closed walk in the Hadamard-transformed matrix. -/
theorem matrix_trace_strict_from_signed_path {I J : Type*}
    [Fintype I] [DecidableEq I] (A : Matrix (I ⊕ I) (I ⊕ I) ℝ)
    (f : J → I) (R : J → J → Prop) (hsym : ∀ {x y}, R x y → R y x) (c d : J → ℝ)
    (hedge : ∀ x y, R x y → ∀ s t,
      A (pathLayer s (f x)) (pathLayer t (f y)) = if s = t then c y else d y)
    (a b : J) (middle : List J) (hpath : (a :: middle ++ [b]).IsChain R)
    (hc : ∀ i ∈ middle, 0 < c i) (hopposite : d a * d b < 0) :
    Matrix.trace (A ^ (2 * (middle.length + 1))) <
      Matrix.trace (absoluteMatrix A ^ (2 * (middle.length + 1))) := by
  let forward := middle.map (fun x => pathLayer true (f x)) ++ [pathLayer false (f b)]
  let returnMiddle := middle.reverse.map (fun x => pathLayer false (f x))
  let cycleMiddle := forward ++ returnMiddle
  let root := pathLayer true (f a)
  have hreverse := reverse_chain_ends R hsym a b middle hpath
  have hw : travelWeight A root (cycleMiddle ++ [root]) =
      ((middle.map c).prod) ^ 2 * (d a * d b) := by
    change travelWeight A (pathLayer true (f a))
      ((forward ++ returnMiddle) ++ [pathLayer true (f a)]) = _
    rw [List.append_assoc, travelWeight_append]
    have hlast : forward.getLastD (pathLayer true (f a)) = pathLayer false (f b) :=
      getLastD_append_one _ _ _
    rw [hlast]
    dsimp only [forward, returnMiddle]
    rw [lifted_path_weight A f R c d hedge a b middle hpath true false,
      lifted_path_weight A f R c d hedge b a middle.reverse hreverse false true]
    norm_num [List.map_reverse, List.prod_reverse]
    ring
  have hneg : travelWeight A root (cycleMiddle ++ [root]) < 0 := by
    rw [hw]
    exact mul_neg_of_pos_of_neg (pow_pos (list_prod_map_pos c middle hc) 2) hopposite
  have h := matrix_trace_strict_of_negative_loop A root cycleMiddle hneg
  have hlength : cycleMiddle.length + 1 = 2 * (middle.length + 1) := by
    simp only [cycleMiddle, forward, returnMiddle, List.length_append,
      List.length_map, List.length_reverse, List.length_singleton]
    omega
  rw [hlength] at h
  exact h

theorem walk_support_prefix {J : Type*} {G : SimpleGraph J} {a b : J} (p : G.Walk a b) :
    ∃ middle : List J, p.support = middle ++ [b] := by
  induction p with
  | nil => exact ⟨[], rfl⟩
  | @cons a x b h q ih =>
    obtain ⟨middle, hm⟩ := ih
    exact ⟨a :: middle, by rw [SimpleGraph.Walk.support_cons, hm]; rfl⟩

/-- The negative-loop witness comes from an actual graph walk. -/
theorem matrix_trace_strict_from_walk {I J : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix (I ⊕ I) (I ⊕ I) ℝ) (f : J → I) (G : SimpleGraph J) (c d : J → ℝ)
    (hedge : ∀ x y, G.Adj x y → ∀ s t,
      A (pathLayer s (f x)) (pathLayer t (f y)) = if s = t then c y else d y)
    (hc : ∀ j, 0 < c j) {a b : J} (p : G.Walk a b) (hopposite : d a * d b < 0) :
    ∃ k : ℕ, 0 < k ∧ Matrix.trace (A ^ (2 * k)) < Matrix.trace (absoluteMatrix A ^ (2 * k)) := by
  cases p with
  | nil => nlinarith [sq_nonneg (d a)]
  | @cons _ y _ h q =>
    obtain ⟨middle, hm⟩ := walk_support_prefix q
    have hpath : (a :: middle ++ [b]).IsChain G.Adj := by
      have hp := (q.cons h).isChain_adj_support
      simpa only [SimpleGraph.Walk.support_cons, hm, List.cons_append] using hp
    exact ⟨middle.length + 1, by omega,
      matrix_trace_strict_from_signed_path A f G.Adj G.adj_symm c d hedge
        a b middle hpath (fun j _ => hc j) hopposite⟩

def preferredDomain (U : Domain) (reflect : Vertex → Vertex)
    (preferred : Vertex → Prop) [DecidablePred preferred] : Domain :=
  (polarized U reflect preferred).filter preferred

def OppositeSingletons (U : Domain) (reflect : Vertex → Vertex) (a b : Vertex) : Prop :=
  (a ∈ U ∧ reflect a ∉ U ∧ b ∉ U ∧ reflect b ∈ U) ∨
    (a ∉ U ∧ reflect a ∈ U ∧ b ∈ U ∧ reflect b ∉ U)

theorem oppositeSingletons_difference (U : Domain) (reflect : Vertex → Vertex) (a b : Vertex)
    (h : OppositeSingletons U reflect a b) :
    ((occupancy U a - occupancy U (reflect a)) / 4) *
      ((occupancy U b - occupancy U (reflect b)) / 4) < 0 := by
  rcases h with ⟨ha, hra, hb, hrb⟩ | ⟨ha, hra, hb, hrb⟩ <;>
    norm_num [occupancy, ha, hra, hb, hrb]

theorem preferred_occupancy_mean_pos {U : Domain} {reflect : Vertex → Vertex}
    (hr : Function.Involutive reflect) (preferred : Vertex → Prop) [DecidablePred preferred]
    (x : preferredDomain U reflect preferred) :
    0 < (occupancy U x.val + occupancy U (reflect x.val)) / 4 := by
  have hx := Finset.mem_filter.mp x.property
  have hu := (mem_polarized hr x.val).mp hx.1
  rw [ite_eq_left hx.2] at hu
  rcases hu with h | h <;> unfold occupancy <;> simp only [h, ite_true]
  all_goals split_ifs <;> norm_num

theorem transformedPair_trace_eq {I : Type*} [Fintype I] [DecidableEq I]
    (S C : Matrix I I ℝ) (u v : I → ℝ) (n : ℕ) :
    Matrix.trace (transformedPairMatrix S C (fun i => (u i + v i) / 2)
      (fun i => (u i - v i) / 2) ^ n) = Matrix.trace (weightedPairMatrix S C u v ^ n) := by
  rw [← pairHadamard_transform]
  exact trace_conjugate_pow _ _ _ pairHadamard_half_inverse.1 pairHadamard_half_inverse.2 n

/-- Strict pair-kernel polarization witnessed by an actual graph walk. -/
theorem weightedPair_strict_from_walk {I J : Type*} [Fintype I] [DecidableEq I]
    (S C : Matrix I I ℝ) (u v : I → ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (hS : ∀ i j, C i j ≤ S i j)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (f : J → I) (G : SimpleGraph J)
    (hedge : ∀ x y, G.Adj x y → S (f x) (f y) = 1 ∧ C (f x) (f y) = 0)
    (hmean : ∀ j, 0 < u (f j) + v (f j)) {a b : J} (p : G.Walk a b)
    (hopposite : (u (f a) - v (f a)) * (u (f b) - v (f b)) < 0) :
    ∃ k : ℕ, 0 < k ∧
      Matrix.trace (weightedPairMatrix S C u v ^ (2 * k)) <
        Matrix.trace (weightedPairMatrix S C (fun i => max (u i) (v i))
          (fun i => min (u i) (v i)) ^ (2 * k)) := by
  let c := fun i => (u i + v i) / 2
  let d := fun i => (u i - v i) / 2
  let A := transformedPairMatrix S C c d
  have hedgeA : ∀ x y, G.Adj x y → ∀ s t,
      A (pathLayer s (f x)) (pathLayer t (f y)) = if s = t then c (f y) else d (f y) := by
    intro x y hxy s t
    obtain ⟨hxyS, hxyC⟩ := hedge x y hxy
    cases s <;> cases t <;>
      simp [A, pathLayer, transformedPairMatrix, Matrix.mul_diagonal, hxyS, hxyC]
  have hc : ∀ j, 0 < c (f j) := fun j => div_pos (hmean j) (by norm_num)
  have hd : d (f a) * d (f b) < 0 := by dsimp [d]; nlinarith
  obtain ⟨k, hk, hstrict⟩ := matrix_trace_strict_from_walk A f G
    (fun j => c (f j)) (fun j => d (f j)) hedgeA hc p hd
  have habs : absoluteMatrix A = transformedPairMatrix S C c (fun i => |d i|) := by
    ext i j
    exact transformedPairMatrix_abs S C c d hC hS
      (fun i => div_nonneg (add_nonneg (hu i) (hv i)) (by norm_num)) i j
  have hleft : Matrix.trace (A ^ (2 * k)) = Matrix.trace (weightedPairMatrix S C u v ^ (2 * k)) :=
    transformedPair_trace_eq S C u v (2 * k)
  have hright := transformedPair_trace_eq S C (fun i => max (u i) (v i))
    (fun i => min (u i) (v i)) (2 * k)
  simp only [max_add_min, max_min_difference] at hright
  rw [hleft, habs, hright] at hstrict
  exact ⟨k, hk, hstrict⟩

/-- Strictness passes through the fixed-point-safe folded cover. -/
theorem weightedKernel_strict_from_walk {I J : Type*} [Fintype I] [DecidableEq I]
    (reflect : I → I) (preferred : I → Prop) (hr : Function.Involutive reflect)
    (hside : ∀ i, preferred (reflect i) ↔ ¬preferred i ∧ reflect i ≠ i)
    (K : Matrix I I ℝ) (hK : ∀ i j, K (reflect i) (reflect j) = K i j)
    (hKn : ∀ i j, 0 ≤ K i j)
    (hdom : ∀ i j,
      K (foldToPreferred reflect preferred i) (reflect (foldToPreferred reflect preferred j)) ≤
        K (foldToPreferred reflect preferred i) (foldToPreferred reflect preferred j))
    (u : I → ℝ) (hu : ∀ i, 0 ≤ u i)
    (f : J → I) (G : SimpleGraph J)
    (hfixed : ∀ j, foldToPreferred reflect preferred (f j) = f j)
    (hedge : ∀ x y, G.Adj x y → K (f x) (f y) = 1 ∧ K (f x) (reflect (f y)) = 0)
    (hmean : ∀ j, 0 < u (f j) + u (reflect (f j))) {a b : J} (p : G.Walk a b)
    (hopposite : (u (f a) - u (reflect (f a))) * (u (f b) - u (reflect (f b))) < 0) :
    ∃ k : ℕ, 0 < k ∧ Matrix.trace (weightedKernel K u ^ (2 * k)) <
      Matrix.trace (weightedKernel K (polarizeWeight reflect preferred u) ^ (2 * k)) := by
  let fold := foldToPreferred reflect preferred
  let S : Matrix I I ℝ := fun i j => K (fold i) (fold j)
  let C : Matrix I I ℝ := fun i j => K (fold i) (reflect (fold j))
  let plus := fun i => u (fold i) / 2
  let minus := fun i => u (reflect (fold i)) / 2
  have hedge' : ∀ x y, G.Adj x y → S (f x) (f y) = 1 ∧ C (f x) (f y) = 0 := by
    intro x y hxy
    simpa only [S, C, fold, hfixed] using hedge x y hxy
  have hmean' : ∀ j, 0 < plus (f j) + minus (f j) := by
    intro j
    dsimp only [plus, minus, fold]
    rw [hfixed]
    have := hmean j
    linarith
  have hopp' : (plus (f a) - minus (f a)) * (plus (f b) - minus (f b)) < 0 := by
    dsimp only [plus, minus, fold]
    rw [hfixed, hfixed]
    nlinarith
  obtain ⟨k, hk, hstrict⟩ := weightedPair_strict_from_walk S C plus minus
    (fun i j => hKn _ _) hdom (fun i => div_nonneg (hu _) (by norm_num))
    (fun i => div_nonneg (hu _) (by norm_num)) f G hedge' hmean' p hopp'
  have hp (i : I) : max (plus i) (minus i) = polarizeWeight reflect preferred u (fold i) / 2 := by
    rw [(polarizeWeight_fold reflect preferred hr hside u i).1]
    exact max_div_div_right (by norm_num : (0 : ℝ) ≤ 2) _ _
  have hm (i : I) : min (plus i) (minus i) =
      polarizeWeight reflect preferred u (reflect (fold i)) / 2 := by
    rw [(polarizeWeight_fold reflect preferred hr hside u i).2]
    exact min_div_div_right (by norm_num : (0 : ℝ) ≤ 2) _ _
  simp_rw [hp, hm] at hstrict
  have hn : 2 * k = (2 * k - 1) + 1 := by omega
  rw [hn] at hstrict
  rw [← weightedKernel_trace_eq_pair reflect fold hr (foldToPreferred_choice reflect preferred) K hK u,
    ← weightedKernel_trace_eq_pair reflect fold hr (foldToPreferred_choice reflect preferred) K hK
      (polarizeWeight reflect preferred u)] at hstrict
  rw [← hn] at hstrict
  exact ⟨k, hk, hstrict⟩

/-- Actual preferred-domain paths give strict induced-domain moments. -/
theorem domainKernel_strict_from_preferred_walk (U : Domain) (reflect : Vertex → Vertex)
    (preferred : Vertex → Prop) [DecidablePred preferred] (hr : Function.Involutive reflect)
    (hside : ∀ x, preferred (reflect x) ↔ ¬preferred x ∧ reflect x ≠ x)
    (K : Vertex → Vertex → ℝ) (hK : ∀ x y, K (reflect x) (reflect y) = K x y)
    (hKn : ∀ x y, 0 ≤ K x y)
    (hdom : ∀ x y,
      K (foldToPreferred reflect preferred x) (reflect (foldToPreferred reflect preferred y)) ≤
        K (foldToPreferred reflect preferred x) (foldToPreferred reflect preferred y))
    (hedge : ∀ x y, preferred x → preferred y → lattice.Adj x y →
      K x y = 1 ∧ K x (reflect y) = 0)
    {a b : preferredDomain U reflect preferred}
    (p : (domainGraph (preferredDomain U reflect preferred)).Walk a b)
    (hopposite : OppositeSingletons U reflect a.val b.val) :
    ∃ k : ℕ, 0 < k ∧ Matrix.trace (domainKernel K U ^ (2 * k)) <
      Matrix.trace (domainKernel K (polarized U reflect preferred) ^ (2 * k)) := by
  classical
  let V := reflectionClosure U reflect
  have hUV : U ⊆ V := Finset.subset_union_left
  have hPV : polarized U reflect preferred ⊆ V := polarized_subset_closure U reflect preferred
  have hJV : preferredDomain U reflect preferred ⊆ V :=
    Finset.Subset.trans (Finset.filter_subset _ _) hPV
  let f := domainInclusion hJV
  have hfix (j : preferredDomain U reflect preferred) :
      foldToPreferred (closureReflection hr) (fun i => preferred i.val) (f j) = f j := by
    have hj : preferred (f j).val := (Finset.mem_filter.mp j.property).2
    simp [foldToPreferred, hj]
  have hedge' : ∀ x y, (domainGraph (preferredDomain U reflect preferred)).Adj x y →
      domainKernel K V (f x) (f y) = 1 ∧
        domainKernel K V (f x) (closureReflection hr (f y)) = 0 := by
    intro x y hxy
    exact hedge x.val y.val (Finset.mem_filter.mp x.property).2
      (Finset.mem_filter.mp y.property).2 hxy
  have hmean (j : preferredDomain U reflect preferred) :
      0 < occupancy U (f j).val + occupancy U (closureReflection hr (f j)).val := by
    have hj := preferred_occupancy_mean_pos hr preferred j
    change 0 < occupancy U j.val + occupancy U (reflect j.val)
    linarith
  have hopp :
      (occupancy U (f a).val - occupancy U (closureReflection hr (f a)).val) *
        (occupancy U (f b).val - occupancy U (closureReflection hr (f b)).val) < 0 := by
    have hh := oppositeSingletons_difference U reflect a.val b.val hopposite
    change (occupancy U a.val - occupancy U (reflect a.val)) *
      (occupancy U b.val - occupancy U (reflect b.val)) < 0
    nlinarith
  obtain ⟨k, hk, hstrict⟩ := weightedKernel_strict_from_walk
    (closureReflection (U := U) hr) (fun j => preferred j.val)
    (closureReflection_involutive hr) (closureReflection_side hr preferred hside)
    (domainKernel K V) (fun i j => hK i.val j.val) (fun i j => hKn i.val j.val)
    (by
      intro i j
      change K _ (reflect _) ≤ K _ _
      simp only [closureReflection_fold]
      exact hdom i.val j.val)
    (fun j => occupancy U j.val) (fun j => occupancy_nonneg U j.val)
    f (domainGraph (preferredDomain U reflect preferred)) hfix hedge' hmean p hopp
  have hv : polarizeWeight (closureReflection (U := U) hr) (fun j => preferred j.val)
      (fun j => occupancy U j.val) = fun j => occupancy (polarized U reflect preferred) j.val :=
    funext (closure_polarizeWeight hr preferred)
  rw [hv] at hstrict
  have hn : 2 * k = (2 * k - 1) + 1 := by omega
  rw [hn] at hstrict
  rw [← domainKernel_trace_ambient K hUV, ← domainKernel_trace_ambient K hPV] at hstrict
  rw [← hn] at hstrict
  exact ⟨k, hk, hstrict⟩

theorem axial_holding_edge (c : ℤ) (x y : Vertex) (hx : c < 2 * x.2) (hy : c < 2 * y.2)
    (hxy : lattice.Adj x y) : holdingKernel x y = 1 ∧ holdingKernel x (axialReflection c y) = 0 := by
  have hne : x ≠ y := lattice.ne_of_adj hxy
  have hn : ¬lattice.Adj x (axialReflection c y) :=
    fun h => hne (axial_cross_adj_eq c x y hx hy h)
  have hnr : x ≠ axialReflection c y := by
    intro heq
    have he := congrArg Prod.snd heq
    dsimp [axialReflection] at he
    omega
  constructor <;> simp [holdingKernel, adjacencyKernel, hne, hxy, hn, hnr]

theorem axial_holding_strict_moments (U : Domain) (c : ℤ)
    {a b : preferredDomain U (axialReflection c) (fun x => c < 2 * x.2)}
    (p : (domainGraph (preferredDomain U (axialReflection c) (fun x => c < 2 * x.2))).Walk a b)
    (hopposite : OppositeSingletons U (axialReflection c) a.val b.val) :
    ∃ k : ℕ, 0 < k ∧ Matrix.trace (domainKernel holdingKernel U ^ (2 * k)) <
      Matrix.trace (domainKernel holdingKernel
        (polarized U (axialReflection c) (fun x => c < 2 * x.2)) ^ (2 * k)) := by
  apply domainKernel_strict_from_preferred_walk U _ _ (axialReflection_involutive c)
    (axial_preferred_side c) holdingKernel (axial_holdingKernel_invariant c) holdingKernel_nonneg
    (fun x y => axial_holdingKernel_closed_domination c _ _
      (axial_fold_preferred c x) (axial_fold_preferred c y)) (axial_holding_edge c) p hopposite

theorem ordinary_strict_from_preferred_walk (U : Domain) (reflect : Vertex → Vertex)
    (preferred : Vertex → Prop) [DecidablePred preferred] (hr : Function.Involutive reflect)
    (hside : ∀ x, preferred (reflect x) ↔ ¬preferred x ∧ reflect x ≠ x)
    (ha : ∀ x y, lattice.Adj (reflect x) (reflect y) ↔ lattice.Adj x y)
    (hcross : ∀ x y, preferred x → preferred y → ¬lattice.Adj x (reflect y))
    {a b : preferredDomain U reflect preferred}
    (p : (domainGraph (preferredDomain U reflect preferred)).Walk a b)
    (hopposite : OppositeSingletons U reflect a.val b.val) :
    ∃ k : ℕ, 0 < k ∧ Matrix.trace (domainKernel adjacencyKernel U ^ (2 * k)) <
      Matrix.trace (domainKernel adjacencyKernel (polarized U reflect preferred) ^ (2 * k)) := by
  classical
  have hK := adjacencyKernel_invariant_of_adj reflect ha
  apply domainKernel_strict_from_preferred_walk U reflect preferred hr hside adjacencyKernel hK
    adjacencyKernel_nonneg _ _ p hopposite
  · intro x y
    rcases fold_preferred_or_fixed reflect preferred hr hside x with hx | hx
    · rcases fold_preferred_or_fixed reflect preferred hr hside y with hy | hy
      · have hn := hcross _ _ hx hy
        change (if lattice.Adj _ _ then (1 : ℝ) else 0) ≤ adjacencyKernel _ _
        rw [ite_eq_right hn]
        exact adjacencyKernel_nonneg _ _
      · rw [hy]
    · exact le_of_eq (by simpa only [hx] using (hK
        (foldToPreferred reflect preferred x) (foldToPreferred reflect preferred y)))
  · intro x y hx hy hxy
    simp [adjacencyKernel, hxy, hcross x y hx hy]

theorem shiftedDiagonal_strict_moments (U : Domain) (c : ℤ)
    {a b : preferredDomain U (shiftedDiagonalReflection c) (fun x => x.1 + c < x.2)}
    (p : (domainGraph (preferredDomain U (shiftedDiagonalReflection c) (fun x => x.1 + c < x.2))).Walk a b)
    (hopposite : OppositeSingletons U (shiftedDiagonalReflection c) a.val b.val) :
    ∃ k : ℕ, 0 < k ∧ Matrix.trace (domainKernel adjacencyKernel U ^ (2 * k)) <
      Matrix.trace (domainKernel adjacencyKernel
        (polarized U (shiftedDiagonalReflection c) (fun x => x.1 + c < x.2)) ^ (2 * k)) :=
  ordinary_strict_from_preferred_walk U _ _ (shiftedDiagonal_involutive c)
    (shiftedDiagonal_side c) (shiftedDiagonal_adj c) (shiftedDiagonal_no_cross c) p hopposite

theorem antiDiagonal_strict_moments (U : Domain) (c : ℤ)
    {a b : preferredDomain U (antiDiagonalReflection c) (fun x => x.1 + x.2 < c)}
    (p : (domainGraph (preferredDomain U (antiDiagonalReflection c) (fun x => x.1 + x.2 < c))).Walk a b)
    (hopposite : OppositeSingletons U (antiDiagonalReflection c) a.val b.val) :
    ∃ k : ℕ, 0 < k ∧ Matrix.trace (domainKernel adjacencyKernel U ^ (2 * k)) <
      Matrix.trace (domainKernel adjacencyKernel
        (polarized U (antiDiagonalReflection c) (fun x => x.1 + x.2 < c)) ^ (2 * k)) :=
  ordinary_strict_from_preferred_walk U _ _ (antiDiagonal_involutive c)
    (antiDiagonal_side c) (antiDiagonal_adj c) (antiDiagonal_no_cross c) p hopposite

open scoped Classical in
theorem adjacency_strict_determinant_of_domain_moments (U V : Domain) (hcard : U.card = V.card)
    (htrace : ∀ n : ℕ, Matrix.trace (domainKernel adjacencyKernel U ^ (n + 1)) ≤
      Matrix.trace (domainKernel adjacencyKernel V ^ (n + 1)))
    (hstrict : ∃ k : ℕ, 0 < k ∧ Matrix.trace (domainKernel adjacencyKernel U ^ (2 * k)) <
      Matrix.trace (domainKernel adjacencyKernel V ^ (2 * k)))
    (z : ℝ) (hz : 4 ≤ z) :
    Matrix.det (z • (1 : Matrix V V ℝ) - (domainGraph V).adjMatrix ℝ) <
      Matrix.det (z • (1 : Matrix U U ℝ) - (domainGraph U).adjMatrix ℝ) := by
  apply DeterminantComparison.determinant_lt_of_trace_lt
    (DomainSpectral.adjacency_isHermitian U) (DomainSpectral.adjacency_isHermitian V)
    (by linarith : 0 < z)
    (fun i => (DomainSpectral.adjacency_eigenvalues_bound U i).trans_le hz)
    (fun i => (DomainSpectral.adjacency_eigenvalues_bound V i).trans_le hz)
    (by simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hcard)
    (fun n => by simpa only [domainKernel_adjacency] using htrace n)
  obtain ⟨k, hk, hs⟩ := hstrict
  refine ⟨2 * k - 1, ?_⟩
  rw [show 2 * k - 1 + 1 = 2 * k by omega]
  simpa only [domainKernel_adjacency] using hs

open scoped Classical in
theorem holding_strict_determinant_of_domain_moments (U V : Domain) (hcard : U.card = V.card)
    (htrace : ∀ n : ℕ, Matrix.trace (domainKernel holdingKernel U ^ (n + 1)) ≤
      Matrix.trace (domainKernel holdingKernel V ^ (n + 1)))
    (hstrict : ∃ k : ℕ, 0 < k ∧ Matrix.trace (domainKernel holdingKernel U ^ (2 * k)) <
      Matrix.trace (domainKernel holdingKernel V ^ (2 * k)))
    (z : ℝ) (hz : 4 ≤ z) :
    Matrix.det (z • (1 : Matrix V V ℝ) - (domainGraph V).adjMatrix ℝ) <
      Matrix.det (z • (1 : Matrix U U ℝ) - (domainGraph U).adjMatrix ℝ) := by
  have hex : ∃ n : ℕ,
      Matrix.trace ((1 + (domainGraph U).adjMatrix ℝ) ^ (n + 1)) <
        Matrix.trace ((1 + (domainGraph V).adjMatrix ℝ) ^ (n + 1)) := by
    obtain ⟨k, hk, hs⟩ := hstrict
    refine ⟨2 * k - 1, ?_⟩
    rw [show 2 * k - 1 + 1 = 2 * k by omega]
    simpa only [domainKernel_holding] using hs
  have h := DeterminantComparison.determinant_lt_of_trace_lt
    (DomainSpectral.holding_isHermitian U) (DomainSpectral.holding_isHermitian V)
    (c := z + 1) (by linarith : 0 < z + 1)
    (fun i => (DomainSpectral.holding_eigenvalues_bound U i).trans_le (by linarith))
    (fun i => (DomainSpectral.holding_eigenvalues_bound V i).trans_le (by linarith))
    (by simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hcard)
    (fun n => by simpa only [domainKernel_holding] using htrace n) hex
  simpa only [det_shift_holding] using h

open scoped Classical in
theorem axial_determinant_strict (U : Domain) (c : ℤ) (z : ℝ) (hz : 4 ≤ z)
    {a b : preferredDomain U (axialReflection c) (fun x => c < 2 * x.2)}
    (p : (domainGraph (preferredDomain U (axialReflection c) (fun x => c < 2 * x.2))).Walk a b)
    (hopposite : OppositeSingletons U (axialReflection c) a.val b.val) :
    let P := polarized U (axialReflection c) (fun x => c < 2 * x.2)
    Matrix.det (z • (1 : Matrix P P ℝ) - (domainGraph P).adjMatrix ℝ) <
      Matrix.det (z • (1 : Matrix U U ℝ) - (domainGraph U).adjMatrix ℝ) := by
  apply holding_strict_determinant_of_domain_moments
  · exact (card_polarized (axialReflection_involutive c) _ (axial_preferred_side c)).symm
  · intro n
    exact axial_holding_moments U c (n + 1)
  · exact axial_holding_strict_moments U c p hopposite
  · exact hz

open scoped Classical in
theorem shiftedDiagonal_determinant_strict (U : Domain) (c : ℤ) (z : ℝ) (hz : 4 ≤ z)
    {a b : preferredDomain U (shiftedDiagonalReflection c) (fun x => x.1 + c < x.2)}
    (p : (domainGraph (preferredDomain U (shiftedDiagonalReflection c) (fun x => x.1 + c < x.2))).Walk a b)
    (hopposite : OppositeSingletons U (shiftedDiagonalReflection c) a.val b.val) :
    let P := polarized U (shiftedDiagonalReflection c) (fun x => x.1 + c < x.2)
    Matrix.det (z • (1 : Matrix P P ℝ) - (domainGraph P).adjMatrix ℝ) <
      Matrix.det (z • (1 : Matrix U U ℝ) - (domainGraph U).adjMatrix ℝ) := by
  apply adjacency_strict_determinant_of_domain_moments
  · exact (card_polarized (shiftedDiagonal_involutive c) _ (shiftedDiagonal_side c)).symm
  · intro n
    exact shiftedDiagonal_adjacency_moments U c (n + 1)
  · exact shiftedDiagonal_strict_moments U c p hopposite
  · exact hz

open scoped Classical in
theorem antiDiagonal_determinant_strict (U : Domain) (c : ℤ) (z : ℝ) (hz : 4 ≤ z)
    {a b : preferredDomain U (antiDiagonalReflection c) (fun x => x.1 + x.2 < c)}
    (p : (domainGraph (preferredDomain U (antiDiagonalReflection c) (fun x => x.1 + x.2 < c))).Walk a b)
    (hopposite : OppositeSingletons U (antiDiagonalReflection c) a.val b.val) :
    let P := polarized U (antiDiagonalReflection c) (fun x => x.1 + x.2 < c)
    Matrix.det (z • (1 : Matrix P P ℝ) - (domainGraph P).adjMatrix ℝ) <
      Matrix.det (z • (1 : Matrix U U ℝ) - (domainGraph U).adjMatrix ℝ) := by
  apply adjacency_strict_determinant_of_domain_moments
  · exact (card_polarized (antiDiagonal_involutive c) _ (antiDiagonal_side c)).symm
  · intro n
    exact antiDiagonal_adjacency_moments U c (n + 1)
  · exact antiDiagonal_strict_moments U c p hopposite
  · exact hz

theorem vertical_holding_edge (c : ℤ) (x y : Vertex) (hx : c < 2 * x.1) (hy : c < 2 * y.1)
    (hxy : lattice.Adj x y) : holdingKernel x y = 1 ∧ holdingKernel x (verticalReflection c y) = 0 := by
  have h := axial_holding_edge c x.swap y.swap hx hy ((diagonal_adjacency_invariant x y).mpr hxy)
  constructor
  · simpa only [holdingKernel_swap] using h.1
  · calc
      holdingKernel x (verticalReflection c y) = holdingKernel x.swap (axialReflection c y.swap) :=
        (holdingKernel_swap x (verticalReflection c y)).symm
      _ = 0 := h.2

theorem vertical_holding_strict_moments (U : Domain) (c : ℤ)
    {a b : preferredDomain U (verticalReflection c) (fun x => c < 2 * x.1)}
    (p : (domainGraph (preferredDomain U (verticalReflection c) (fun x => c < 2 * x.1))).Walk a b)
    (hopposite : OppositeSingletons U (verticalReflection c) a.val b.val) :
    ∃ k : ℕ, 0 < k ∧ Matrix.trace (domainKernel holdingKernel U ^ (2 * k)) <
      Matrix.trace (domainKernel holdingKernel
        (polarized U (verticalReflection c) (fun x => c < 2 * x.1)) ^ (2 * k)) := by
  exact domainKernel_strict_from_preferred_walk U _ _ (vertical_involutive c)
    (vertical_preferred_side c) holdingKernel (vertical_holdingKernel_invariant c) holdingKernel_nonneg
    (fun x y => vertical_holdingKernel_closed_domination c _ _
      (vertical_fold_preferred c x) (vertical_fold_preferred c y)) (vertical_holding_edge c) p hopposite

open scoped Classical in
theorem vertical_determinant_strict (U : Domain) (c : ℤ) (z : ℝ) (hz : 4 ≤ z)
    {a b : preferredDomain U (verticalReflection c) (fun x => c < 2 * x.1)}
    (p : (domainGraph (preferredDomain U (verticalReflection c) (fun x => c < 2 * x.1))).Walk a b)
    (hopposite : OppositeSingletons U (verticalReflection c) a.val b.val) :
    let P := polarized U (verticalReflection c) (fun x => c < 2 * x.1)
    Matrix.det (z • (1 : Matrix P P ℝ) - (domainGraph P).adjMatrix ℝ) <
      Matrix.det (z • (1 : Matrix U U ℝ) - (domainGraph U).adjMatrix ℝ) := by
  apply holding_strict_determinant_of_domain_moments
  · exact (card_polarized (vertical_involutive c) _ (vertical_preferred_side c)).symm
  · intro n
    exact vertical_holding_moments U c (n + 1)
  · exact vertical_holding_strict_moments U c p hopposite
  · exact hz

end SpanningTreeIsoperimetry.Polarization






