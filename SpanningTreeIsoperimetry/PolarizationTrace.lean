module

public import SpanningTreeIsoperimetry.Polarization
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

/-! Matrix trace form of two-point polarization. -/

namespace SpanningTreeIsoperimetry.Polarization

open scoped BigOperators

theorem matrix_abs_pow_le {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℝ) (h : ∀ i j, |A i j| ≤ B i j) (n : ℕ) :
    ∀ i j, |(A ^ n) i j| ≤ (B ^ n) i j := by
  have hB : ∀ i j, 0 ≤ B i j := fun i j => (abs_nonneg _).trans (h i j)
  induction n with
  | zero => intro i j; simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    intro i j
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    calc
      |∑ k, (A ^ n) i k * A k j| ≤ ∑ k, |(A ^ n) i k * A k j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, (B ^ n) i k * B k j := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_mul (ih i k) (h k j) (abs_nonneg _) (Matrix.pow_apply_nonneg hB n i k)

theorem matrix_trace_pow_le_of_abs_le {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℝ) (h : ∀ i j, |A i j| ≤ B i j) (n : ℕ) :
    Matrix.trace (A ^ n) ≤ Matrix.trace (B ^ n) := by
  apply Finset.sum_le_sum
  intro i _
  exact (le_abs_self _).trans (matrix_abs_pow_le A B h n i i)

theorem trace_conjugate_pow {I : Type*} [Fintype I] [DecidableEq I]
    (L R A : Matrix I I ℝ) (hLR : L * R = 1) (hRL : R * L = 1) (n : ℕ) :
    Matrix.trace ((L * A * R) ^ n) = Matrix.trace (A ^ n) := by
  have hp (k : ℕ) : (L * A * R) ^ k = L * A ^ k * R := by
    induction k with
    | zero => simp [hLR]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      calc
        L * A ^ k * R * (L * A * R) = L * A ^ k * (R * L) * A * R := by noncomm_ring
        _ = L * (A ^ k * A) * R := by rw [hRL]; noncomm_ring
  rw [hp, Matrix.trace_mul_cycle, hRL, one_mul]

def pairHadamard {I : Type*} [Fintype I] [DecidableEq I] : Matrix (I ⊕ I) (I ⊕ I) ℝ :=
  Matrix.fromBlocks 1 1 1 (-1)

theorem pairHadamard_square {I : Type*} [Fintype I] [DecidableEq I] :
    (pairHadamard (I := I)) * pairHadamard = (2 : ℝ) • 1 := by
  unfold pairHadamard
  rw [Matrix.fromBlocks_multiply]
  simp only [mul_one, mul_neg, neg_neg, add_neg_cancel]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
  congr 1 <;> module

theorem pairHadamard_half_inverse {I : Type*} [Fintype I] [DecidableEq I] :
    (pairHadamard (I := I)) * ((1 / 2 : ℝ) • pairHadamard) = 1 ∧
      ((1 / 2 : ℝ) • pairHadamard (I := I)) * pairHadamard (I := I) = 1 := by
  constructor <;> simp only [Matrix.mul_smul, Matrix.smul_mul, pairHadamard_square, smul_smul] <;> norm_num

def weightedPairMatrix {I : Type*} [Fintype I] [DecidableEq I]
    (S C : Matrix I I ℝ) (u v : I → ℝ) : Matrix (I ⊕ I) (I ⊕ I) ℝ :=
  Matrix.fromBlocks (S * Matrix.diagonal u) (C * Matrix.diagonal v)
    (C * Matrix.diagonal u) (S * Matrix.diagonal v)

def transformedPairMatrix {I : Type*} [Fintype I] [DecidableEq I]
    (S C : Matrix I I ℝ) (c d : I → ℝ) : Matrix (I ⊕ I) (I ⊕ I) ℝ :=
  Matrix.fromBlocks ((S + C) * Matrix.diagonal c) ((S + C) * Matrix.diagonal d)
    ((S - C) * Matrix.diagonal d) ((S - C) * Matrix.diagonal c)

theorem pairHadamard_transform {I : Type*} [Fintype I] [DecidableEq I]
    (S C : Matrix I I ℝ) (u v : I → ℝ) :
    pairHadamard * weightedPairMatrix S C u v * ((1 / 2 : ℝ) • pairHadamard) =
      transformedPairMatrix S C (fun i => (u i + v i) / 2) (fun i => (u i - v i) / 2) := by
  simp only [pairHadamard, weightedPairMatrix, transformedPairMatrix, Matrix.mul_smul,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, one_mul, neg_mul, mul_neg,
    mul_one]
  congr 1 <;> ext i j <;>
    simp [Matrix.mul_diagonal, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply] <;> ring

theorem transformedPairMatrix_abs {I : Type*} [Fintype I] [DecidableEq I]
    (S C : Matrix I I ℝ) (c d : I → ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (hS : ∀ i j, C i j ≤ S i j) (hc : ∀ i, 0 ≤ c i) :
    ∀ i j, |transformedPairMatrix S C c d i j| =
      transformedPairMatrix S C c (fun i => |d i|) i j := by
  have hsum (i j : I) : 0 ≤ S i j + C i j := add_nonneg ((hC i j).trans (hS i j)) (hC i j)
  have hdiff (i j : I) : 0 ≤ S i j - C i j := sub_nonneg.mpr (hS i j)
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [transformedPairMatrix, Matrix.mul_diagonal, abs_mul,
        abs_of_nonneg (hsum i j), abs_of_nonneg (hc j)]
    | inr j => simp [transformedPairMatrix, Matrix.mul_diagonal, abs_mul,
        abs_of_nonneg (hsum i j)]
  | inr i =>
    cases j with
    | inl j => simp [transformedPairMatrix, Matrix.mul_diagonal, abs_mul,
        abs_of_nonneg (hdiff i j)]
    | inr j => simp [transformedPairMatrix, Matrix.mul_diagonal, abs_mul,
        abs_of_nonneg (hdiff i j), abs_of_nonneg (hc j)]

/-- Trace-power polarization for a finite reflection-pair kernel. -/
theorem weightedPairMatrix_trace_polarization {I : Type*} [Fintype I] [DecidableEq I]
    (S C : Matrix I I ℝ) (u v : I → ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (hS : ∀ i j, C i j ≤ S i j)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) (n : ℕ) :
    Matrix.trace (weightedPairMatrix S C u v ^ n) ≤
      Matrix.trace (weightedPairMatrix S C (fun i => max (u i) (v i))
        (fun i => min (u i) (v i)) ^ n) := by
  have htr (u v : I → ℝ) :
      Matrix.trace (transformedPairMatrix S C (fun i => (u i + v i) / 2)
        (fun i => (u i - v i) / 2) ^ n) = Matrix.trace (weightedPairMatrix S C u v ^ n) := by
    rw [← pairHadamard_transform]
    exact trace_conjugate_pow _ _ _ pairHadamard_half_inverse.1 pairHadamard_half_inverse.2 n
  rw [← htr, ← htr]
  simp only [max_add_min, max_min_difference]
  apply matrix_trace_pow_le_of_abs_le
  intro i j
  exact (transformedPairMatrix_abs S C _ _ hC hS
    (fun i => div_nonneg (add_nonneg (hu i) (hv i)) (by norm_num)) i j).le

theorem trace_rectangular_product_pow {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (X : Matrix I J ℝ) (Y : Matrix J I ℝ) (n : ℕ) :
    Matrix.trace ((X * Y) ^ (n + 1)) = Matrix.trace ((Y * X) ^ (n + 1)) := by
  have hp (k : ℕ) : (X * Y) ^ (k + 1) = X * (Y * X) ^ k * Y := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [hp, Matrix.trace_mul_cycle, ← pow_succ']

/-- The folded two-point cover includes fixed points twice as well. -/
def foldCover {I : Type*} (reflect fold : I → I) : I ⊕ I → I
  | Sum.inl i => fold i
  | Sum.inr i => reflect (fold i)

theorem sum_foldCover {I : Type*} [Fintype I] (reflect fold : I → I)
    (hr : Function.Involutive reflect) (hf : ∀ i, fold i = i ∨ fold i = reflect i)
    (g : I → ℝ) :
    (∑ p : I ⊕ I, g (foldCover reflect fold p)) = 2 * ∑ i, g i := by
  classical
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  have hterm (i : I) : g (fold i) + g (reflect (fold i)) = g i + g (reflect i) := by
    rcases hf i with h | h
    · rw [h]
    · rw [h, hr]; ring
  simp only [foldCover, hterm, Finset.sum_add_distrib]
  have hs : (∑ i, g (reflect i)) = ∑ i, g i :=
    Equiv.sum_comp (Function.Involutive.toPerm reflect hr) g
  rw [hs]
  ring

noncomputable def coverProjection {I : Type*} [DecidableEq I] (reflect fold : I → I) :
    Matrix I (I ⊕ I) ℝ := fun i p => if foldCover reflect fold p = i then 1 / 2 else 0

def coverKernel {I : Type*} (reflect fold : I → I) (K : Matrix I I ℝ) (u : I → ℝ) :
    Matrix (I ⊕ I) I ℝ := fun p j => K (foldCover reflect fold p) j * u j

def weightedKernel {I : Type*} (K : Matrix I I ℝ) (u : I → ℝ) : Matrix I I ℝ :=
  fun i j => K i j * u j

theorem coverProjection_mul_kernel {I : Type*} [Fintype I] [DecidableEq I]
    (reflect fold : I → I) (hr : Function.Involutive reflect)
    (hf : ∀ i, fold i = i ∨ fold i = reflect i) (K : Matrix I I ℝ) (u : I → ℝ) :
    coverProjection reflect fold * coverKernel reflect fold K u = weightedKernel K u := by
  ext i j
  simp only [Matrix.mul_apply, coverProjection, coverKernel, weightedKernel]
  have hsum := sum_foldCover reflect fold hr hf
    (fun x => (if x = i then (1 / 2 : ℝ) else 0) * (K x j * u j))
  rw [hsum]
  simp

theorem kernel_mul_coverProjection {I : Type*} [Fintype I] [DecidableEq I]
    (reflect fold : I → I) (K : Matrix I I ℝ) (u : I → ℝ) :
    coverKernel reflect fold K u * coverProjection reflect fold =
      fun p q => K (foldCover reflect fold p) (foldCover reflect fold q) *
        (u (foldCover reflect fold q) / 2) := by
  ext p q
  simp only [Matrix.mul_apply, coverProjection, coverKernel]
  rw [Finset.sum_eq_single (foldCover reflect fold q)]
  · simp; ring
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

theorem covered_weightedKernel_eq_pair {I : Type*} [Fintype I] [DecidableEq I]
    (reflect fold : I → I) (hr : Function.Involutive reflect)
    (K : Matrix I I ℝ) (hK : ∀ i j, K (reflect i) (reflect j) = K i j) (u : I → ℝ) :
    coverKernel reflect fold K u * coverProjection reflect fold =
      weightedPairMatrix (fun i j => K (fold i) (fold j))
        (fun i j => K (fold i) (reflect (fold j)))
        (fun i => u (fold i) / 2) (fun i => u (reflect (fold i)) / 2) := by
  rw [kernel_mul_coverProjection]
  have hcross (i j : I) : K (reflect i) j = K i (reflect j) := by
    simpa only [hr j] using hK i (reflect j)
  ext p q
  cases p <;> cases q <;>
    simp only [foldCover, weightedPairMatrix, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, hK, hcross]
  all_goals first
    | exact (Matrix.mul_diagonal (fun i => u (fold i) / 2)
        (Matrix.of (fun i j => K (fold i) (fold j))) _ _).symm
    | exact (Matrix.mul_diagonal (fun i => u (reflect (fold i)) / 2)
        (Matrix.of (fun i j => K (fold i) (reflect (fold j)))) _ _).symm
    | exact (Matrix.mul_diagonal (fun i => u (fold i) / 2)
        (Matrix.of (fun i j => K (fold i) (reflect (fold j)))) _ _).symm
    | exact (Matrix.mul_diagonal (fun i => u (reflect (fold i)) / 2)
        (Matrix.of (fun i j => K (fold i) (fold j))) _ _).symm

/-- Exact trace transfer through the doubled cover, including reflection-fixed points. -/
theorem weightedKernel_trace_eq_pair {I : Type*} [Fintype I] [DecidableEq I]
    (reflect fold : I → I) (hr : Function.Involutive reflect)
    (hf : ∀ i, fold i = i ∨ fold i = reflect i)
    (K : Matrix I I ℝ) (hK : ∀ i j, K (reflect i) (reflect j) = K i j)
    (u : I → ℝ) (n : ℕ) :
    Matrix.trace (weightedKernel K u ^ (n + 1)) =
      Matrix.trace (weightedPairMatrix (fun i j => K (fold i) (fold j))
        (fun i j => K (fold i) (reflect (fold j)))
        (fun i => u (fold i) / 2) (fun i => u (reflect (fold i)) / 2) ^ (n + 1)) := by
  rw [← coverProjection_mul_kernel reflect fold hr hf K u]
  rw [trace_rectangular_product_pow, covered_weightedKernel_eq_pair reflect fold hr K hK u]

/-- Abstract finite-kernel polarization. All hypotheses concern the involution,
fold, kernel entries, and the actual two-point occupancy values. -/
theorem weightedKernel_trace_polarization {I : Type*} [Fintype I] [DecidableEq I]
    (reflect fold : I → I) (hr : Function.Involutive reflect)
    (hf : ∀ i, fold i = i ∨ fold i = reflect i)
    (K : Matrix I I ℝ) (hK : ∀ i j, K (reflect i) (reflect j) = K i j)
    (hKn : ∀ i j, 0 ≤ K i j)
    (hdom : ∀ i j, K (fold i) (reflect (fold j)) ≤ K (fold i) (fold j))
    (u v : I → ℝ) (hu : ∀ i, 0 ≤ u i)
    (hp : ∀ i, v (fold i) = max (u (fold i)) (u (reflect (fold i))))
    (hm : ∀ i, v (reflect (fold i)) = min (u (fold i)) (u (reflect (fold i)))) (n : ℕ) :
    Matrix.trace (weightedKernel K u ^ n) ≤ Matrix.trace (weightedKernel K v ^ n) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [weightedKernel_trace_eq_pair reflect fold hr hf K hK u n,
      weightedKernel_trace_eq_pair reflect fold hr hf K hK v n]
    simp only [hp, hm]
    have h := weightedPairMatrix_trace_polarization
      (fun i j => K (fold i) (fold j))
      (fun i j => K (fold i) (reflect (fold j)))
      (fun i => u (fold i) / 2) (fun i => u (reflect (fold i)) / 2)
      (fun i j => hKn _ _) hdom
      (fun i => div_nonneg (hu _) (by norm_num))
      (fun i => div_nonneg (hu _) (by norm_num)) (n + 1)
    simpa only [max_div_div_right (by norm_num : (0 : ℝ) ≤ 2),
      min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)] using h

noncomputable def rangeIndicator {I J : Type*} (f : J → I) (i : I) : ℝ := by
  classical
  exact if ∃ j, f j = i then 1 else 0

noncomputable def inclusionProjection {I J : Type*} (f : J → I) : Matrix J I ℝ := by
  classical
  exact fun j i => if f j = i then 1 else 0

def inclusionKernel {I J : Type*} (K : Matrix I I ℝ) (f : J → I) : Matrix I J ℝ :=
  fun i j => K i (f j)

theorem inclusionKernel_mul_projection {I J : Type*} [Fintype I] [Fintype J]
    (K : Matrix I I ℝ) (f : J → I) (hf : Function.Injective f) :
    inclusionKernel K f * inclusionProjection f = weightedKernel K (rangeIndicator f) := by
  classical
  ext i k
  simp only [Matrix.mul_apply, inclusionKernel, inclusionProjection, weightedKernel, rangeIndicator]
  by_cases h : ∃ j, f j = k
  · obtain ⟨j, rfl⟩ := h
    rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hlj
      simp [hf.ne hlj]
    · simp
  · have hz : ∀ j, f j ≠ k := by simpa using h
    simp [hz]

theorem projection_mul_inclusionKernel {I J : Type*} [Fintype I] [Fintype J]
    (K : Matrix I I ℝ) (f : J → I) :
    inclusionProjection f * inclusionKernel K f = K.submatrix f f := by
  classical
  ext j k
  simp [Matrix.mul_apply, inclusionProjection, inclusionKernel, Matrix.submatrix_apply,
    ite_mul]

/-- Zero-weight ambient vertices do not affect any positive trace moment. -/
theorem weightedKernel_trace_submatrix {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (K : Matrix I I ℝ) (f : J → I)
    (hf : Function.Injective f) (n : ℕ) :
    Matrix.trace (weightedKernel K (rangeIndicator f) ^ (n + 1)) =
      Matrix.trace (K.submatrix f f ^ (n + 1)) := by
  rw [← inclusionKernel_mul_projection K f hf, trace_rectangular_product_pow,
    projection_mul_inclusionKernel K f]

noncomputable def polarizeWeight {I : Type*} (reflect : I → I) (preferred : I → Prop)
    (u : I → ℝ) (i : I) : ℝ := by
  classical
  exact if preferred i then max (u i) (u (reflect i)) else min (u i) (u (reflect i))

noncomputable def foldToPreferred {I : Type*} (reflect : I → I) (preferred : I → Prop) (i : I) : I := by
  classical
  exact if preferred i then i else reflect i

theorem foldToPreferred_choice {I : Type*} (reflect : I → I) (preferred : I → Prop) (i : I) :
    foldToPreferred reflect preferred i = i ∨ foldToPreferred reflect preferred i = reflect i := by
  classical
  unfold foldToPreferred
  split_ifs <;> simp

theorem polarizeWeight_fold {I : Type*} (reflect : I → I) (preferred : I → Prop)
    (hr : Function.Involutive reflect)
    (hside : ∀ i, preferred (reflect i) ↔ ¬preferred i ∧ reflect i ≠ i)
    (u : I → ℝ) (i : I) :
    polarizeWeight reflect preferred u (foldToPreferred reflect preferred i) =
      max (u (foldToPreferred reflect preferred i)) (u (reflect (foldToPreferred reflect preferred i))) ∧
    polarizeWeight reflect preferred u (reflect (foldToPreferred reflect preferred i)) =
      min (u (foldToPreferred reflect preferred i)) (u (reflect (foldToPreferred reflect preferred i))) := by
  classical
  by_cases hp : preferred i
  · have hn : ¬preferred (reflect i) := by rw [hside]; tauto
    simp [foldToPreferred, hp, polarizeWeight, hn, hr i, min_comm]
  · by_cases heq : reflect i = i
    · simp [foldToPreferred, hp, heq, polarizeWeight]
    · have hpr : preferred (reflect i) := (hside i).mpr ⟨hp, heq⟩
      simp [foldToPreferred, hp, polarizeWeight, hpr, hr i, max_comm, min_comm]

/-- Trace comparison for the explicitly defined polarization of an arbitrary
finite reflection kernel; fixed points are included without extra hypotheses. -/
theorem polarizeWeight_trace {I : Type*} [Fintype I] [DecidableEq I]
    (reflect : I → I) (preferred : I → Prop) (hr : Function.Involutive reflect)
    (hside : ∀ i, preferred (reflect i) ↔ ¬preferred i ∧ reflect i ≠ i)
    (K : Matrix I I ℝ) (hK : ∀ i j, K (reflect i) (reflect j) = K i j)
    (hKn : ∀ i j, 0 ≤ K i j)
    (hdom : ∀ i j,
      K (foldToPreferred reflect preferred i) (reflect (foldToPreferred reflect preferred j)) ≤
        K (foldToPreferred reflect preferred i) (foldToPreferred reflect preferred j))
    (u : I → ℝ) (hu : ∀ i, 0 ≤ u i) (n : ℕ) :
    Matrix.trace (weightedKernel K u ^ n) ≤
      Matrix.trace (weightedKernel K (polarizeWeight reflect preferred u) ^ n) := by
  exact weightedKernel_trace_polarization reflect (foldToPreferred reflect preferred) hr
    (foldToPreferred_choice reflect preferred) K hK hKn hdom u _ hu
    (fun i => (polarizeWeight_fold reflect preferred hr hside u i).1)
    (fun i => (polarizeWeight_fold reflect preferred hr hside u i).2) n

theorem sum_polarizeWeight {I : Type*} [Fintype I] [DecidableEq I]
    (reflect : I → I) (preferred : I → Prop) (hr : Function.Involutive reflect)
    (hside : ∀ i, preferred (reflect i) ↔ ¬preferred i ∧ reflect i ≠ i) (u : I → ℝ) :
    (∑ i, polarizeWeight reflect preferred u i) = ∑ i, u i := by
  let fold := foldToPreferred reflect preferred
  have hc := foldToPreferred_choice reflect preferred
  have hu := sum_foldCover reflect fold hr hc u
  have hp := sum_foldCover reflect fold hr hc (polarizeWeight reflect preferred u)
  have hpv (i : I) := (polarizeWeight_fold reflect preferred hr hside u i).1
  have hmv (i : I) := (polarizeWeight_fold reflect preferred hr hside u i).2
  simp only [Fintype.sum_sum_type, foldCover, fold, hpv, hmv] at hu hp
  rw [← Finset.sum_add_distrib] at hu hp
  simp only [max_add_min] at hp
  linarith

/-- Kernel matrix on the actual vertices of a finite lattice domain. -/
def domainKernel (K : Vertex → Vertex → ℝ) (U : Domain) : Matrix U U ℝ :=
  fun i j => K i.val j.val

def domainInclusion {U V : Domain} (hUV : U ⊆ V) : U → V :=
  fun i => ⟨i.val, hUV i.property⟩

theorem domainInclusion_injective {U V : Domain} (hUV : U ⊆ V) :
    Function.Injective (domainInclusion hUV) := by
  intro i j h
  exact Subtype.ext (congrArg (fun x : V => x.val) h)

theorem domainInclusion_range {U V : Domain} (hUV : U ⊆ V) (i : V) :
    rangeIndicator (domainInclusion hUV) i = occupancy U i.val := by
  classical
  have he : (∃ j, domainInclusion hUV j = i) ↔ i.val ∈ U := by
    constructor
    · rintro ⟨j, rfl⟩
      exact j.property
    · intro hi
      exact ⟨⟨i.val, hi⟩, rfl⟩
  simp only [rangeIndicator, he, occupancy]

theorem domainKernel_trace_ambient (K : Vertex → Vertex → ℝ) {U V : Domain}
    (hUV : U ⊆ V) (n : ℕ) :
    Matrix.trace (domainKernel K U ^ (n + 1)) =
      Matrix.trace (weightedKernel (domainKernel K V) (fun i => occupancy U i.val) ^ (n + 1)) := by
  have h := weightedKernel_trace_submatrix (domainKernel K V) (domainInclusion hUV)
    (domainInclusion_injective hUV) n
  have hm : (domainKernel K V).submatrix (domainInclusion hUV) (domainInclusion hUV) =
      domainKernel K U := rfl
  rw [hm] at h
  have hfun : rangeIndicator (domainInclusion hUV) = fun i : V => occupancy U i.val :=
    funext (domainInclusion_range hUV)
  rw [hfun] at h
  exact h.symm

def reflectionClosure (U : Domain) (reflect : Vertex → Vertex) : Domain := U ∪ U.image reflect

theorem mem_reflectionClosure {U : Domain} {reflect : Vertex → Vertex}
    (hr : Function.Involutive reflect) (x : Vertex) :
    x ∈ reflectionClosure U reflect ↔ x ∈ U ∨ reflect x ∈ U := by
  simp only [reflectionClosure, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨y, hy, rfl⟩)
    · exact Or.inl h
    · right
      simpa only [hr y] using hy
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨reflect x, h, hr x⟩

theorem reflectionClosure_invariant {U : Domain} {reflect : Vertex → Vertex}
    (hr : Function.Involutive reflect) {x : Vertex}
    (hx : x ∈ reflectionClosure U reflect) : reflect x ∈ reflectionClosure U reflect := by
  rw [mem_reflectionClosure hr] at hx ⊢
  rw [hr x]
  exact hx.symm

def closureReflection {U : Domain} {reflect : Vertex → Vertex} (hr : Function.Involutive reflect) :
    reflectionClosure U reflect → reflectionClosure U reflect :=
  fun x => ⟨reflect x.val, reflectionClosure_invariant hr x.property⟩

theorem closureReflection_involutive {U : Domain} {reflect : Vertex → Vertex}
    (hr : Function.Involutive reflect) : Function.Involutive (closureReflection (U := U) hr) := by
  intro x
  exact Subtype.ext (hr x.val)

theorem polarized_subset_closure (U : Domain) (reflect : Vertex → Vertex)
    (preferred : Vertex → Prop) [DecidablePred preferred] :
    polarized U reflect preferred ⊆ reflectionClosure U reflect := Finset.filter_subset _ _

theorem polarized_occupancy_eq_weight {U : Domain} {reflect : Vertex → Vertex}
    (hr : Function.Involutive reflect) (preferred : Vertex → Prop) [DecidablePred preferred]
    (x : Vertex) :
    occupancy (polarized U reflect preferred) x =
      polarizeWeight reflect preferred (occupancy U) x := by
  classical
  unfold occupancy polarizeWeight
  simp only [mem_polarized hr]
  by_cases hp : preferred x <;> by_cases hu : x ∈ U <;>
    by_cases hv : reflect x ∈ U <;> simp [hp, hu, hv]

theorem sum_occupancy_ambient {U V : Domain} (hUV : U ⊆ V) :
    (∑ i : V, occupancy U i.val) = (U.card : ℝ) := by
  rw [← Finset.sum_subtype V (fun _ => Iff.rfl) (occupancy U)]
  unfold occupancy
  rw [Finset.sum_boole]
  have hf : V.filter (fun x => x ∈ U) = U := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hx => ⟨hUV hx, hx⟩⟩
  rw [hf]

theorem closureReflection_side {U : Domain} {reflect : Vertex → Vertex}
    (hr : Function.Involutive reflect) (preferred : Vertex → Prop)
    (hside : ∀ x, preferred (reflect x) ↔ ¬preferred x ∧ reflect x ≠ x)
    (i : reflectionClosure U reflect) :
    preferred (closureReflection hr i).val ↔
      ¬preferred i.val ∧ closureReflection hr i ≠ i := by
  simpa only [closureReflection, ne_eq, Subtype.ext_iff] using hside i.val

theorem closureReflection_fold {U : Domain} {reflect : Vertex → Vertex}
    (hr : Function.Involutive reflect) (preferred : Vertex → Prop)
    (i : reflectionClosure U reflect) :
    (foldToPreferred (closureReflection hr) (fun j => preferred j.val) i).val =
      foldToPreferred reflect preferred i.val := by
  classical
  unfold foldToPreferred
  split_ifs <;> rfl

theorem closure_polarizeWeight {U : Domain} {reflect : Vertex → Vertex}
    (hr : Function.Involutive reflect) (preferred : Vertex → Prop) [DecidablePred preferred]
    (i : reflectionClosure U reflect) :
    polarizeWeight (closureReflection hr) (fun j => preferred j.val)
      (fun j => occupancy U j.val) i = occupancy (polarized U reflect preferred) i.val := by
  rw [polarized_occupancy_eq_weight hr]
  rfl

theorem card_polarized {U : Domain} {reflect : Vertex → Vertex}
    (hr : Function.Involutive reflect) (preferred : Vertex → Prop) [DecidablePred preferred]
    (hside : ∀ x, preferred (reflect x) ↔ ¬preferred x ∧ reflect x ≠ x) :
    (polarized U reflect preferred).card = U.card := by
  have h := sum_polarizeWeight (closureReflection (U := U) hr) (fun j => preferred j.val)
    (closureReflection_involutive hr) (closureReflection_side hr preferred hside)
    (fun j => occupancy U j.val)
  simp only [closure_polarizeWeight] at h
  have hp := sum_occupancy_ambient (polarized_subset_closure U reflect preferred)
  have hu := sum_occupancy_ambient
    (Finset.subset_union_left : U ⊆ reflectionClosure U reflect)
  have hc : ((polarized U reflect preferred).card : ℝ) = (U.card : ℝ) :=
    hp.symm.trans (h.trans hu)
  exact_mod_cast hc

/-- Complete finite-domain trace comparison under a reflection kernel's
verified two-point conditions. No trace inequality is supplied as an input. -/
theorem domainKernel_polarization_moments (U : Domain) (reflect : Vertex → Vertex)
    (preferred : Vertex → Prop) [DecidablePred preferred] (hr : Function.Involutive reflect)
    (hside : ∀ x, preferred (reflect x) ↔ ¬preferred x ∧ reflect x ≠ x)
    (K : Vertex → Vertex → ℝ) (hK : ∀ x y, K (reflect x) (reflect y) = K x y)
    (hKn : ∀ x y, 0 ≤ K x y)
    (hdom : ∀ x y,
      K (foldToPreferred reflect preferred x) (reflect (foldToPreferred reflect preferred y)) ≤
        K (foldToPreferred reflect preferred x) (foldToPreferred reflect preferred y)) (n : ℕ) :
    Matrix.trace (domainKernel K U ^ n) ≤
      Matrix.trace (domainKernel K (polarized U reflect preferred) ^ n) := by
  classical
  cases n with
  | zero =>
    simp only [pow_zero, Matrix.trace_one, Fintype.card_coe, Nat.cast_le]
    exact (card_polarized hr preferred hside).ge
  | succ n =>
    let V := reflectionClosure U reflect
    have hUV : U ⊆ V := Finset.subset_union_left
    have hPV : polarized U reflect preferred ⊆ V := polarized_subset_closure U reflect preferred
    rw [domainKernel_trace_ambient K hUV n, domainKernel_trace_ambient K hPV n]
    have htrace := polarizeWeight_trace (closureReflection (U := U) hr)
      (fun j => preferred j.val) (closureReflection_involutive hr)
      (closureReflection_side hr preferred hside) (domainKernel K V)
      (fun i j => hK i.val j.val) (fun i j => hKn i.val j.val)
      (by
        intro i j
        change K _ (reflect _) ≤ K _ _
        simp only [closureReflection_fold]
        exact hdom i.val j.val)
      (fun j => occupancy U j.val) (fun j => occupancy_nonneg U j.val) (n + 1)
    have hv : polarizeWeight (closureReflection (U := U) hr) (fun j => preferred j.val)
        (fun j => occupancy U j.val) = fun j => occupancy (polarized U reflect preferred) j.val :=
      funext (closure_polarizeWeight hr preferred)
    rw [hv] at htrace
    exact htrace

theorem axial_preferred_side (c : ℤ) (x : Vertex) :
    c < 2 * (axialReflection c x).2 ↔ ¬c < 2 * x.2 ∧ axialReflection c x ≠ x := by
  have heq : axialReflection c x = x ↔ c = 2 * x.2 := by
    constructor
    · intro h
      have h' := congrArg Prod.snd h
      dsimp [axialReflection] at h'
      omega
    · intro h
      (apply Prod.ext <;> dsimp [axialReflection])
      omega
  change c < 2 * (c - x.2) ↔ _
  rw [ne_eq, heq]
  omega

theorem axial_holdingKernel_closed_domination (c : ℤ) (x y : Vertex)
    (hx : c ≤ 2 * x.2) (hy : c ≤ 2 * y.2) :
    holdingKernel x (axialReflection c y) ≤ holdingKernel x y := by
  by_cases hx0 : c = 2 * x.2
  · have hfix : axialReflection c x = x := by
      (apply Prod.ext <;> dsimp [axialReflection])
      omega
    exact le_of_eq (by simpa only [hfix] using axial_holdingKernel_invariant c x y)
  · by_cases hy0 : c = 2 * y.2
    · have hfix : axialReflection c y = y := by
        (apply Prod.ext <;> dsimp [axialReflection])
        omega
      rw [hfix]
    · exact axial_holdingKernel_domination c x y (by omega) (by omega)

theorem axial_fold_preferred (c : ℤ) (x : Vertex) :
    c ≤ 2 * (foldToPreferred (axialReflection c) (fun y => c < 2 * y.2) x).2 := by
  classical
  unfold foldToPreferred
  split_ifs with h <;> (try dsimp [axialReflection]) <;> omega

/-- The holding-kernel moment comparison for every horizontal lattice reflection,
including axes through lattice vertices and axes between rows. -/
theorem axial_holding_moments (U : Domain) (c : ℤ) (n : ℕ) :
    Matrix.trace (domainKernel holdingKernel U ^ n) ≤
      Matrix.trace (domainKernel holdingKernel
        (polarized U (axialReflection c) (fun x => c < 2 * x.2)) ^ n) := by
  apply domainKernel_polarization_moments U (axialReflection c) (fun x => c < 2 * x.2)
    (axialReflection_involutive c) (axial_preferred_side c) holdingKernel
    (axial_holdingKernel_invariant c) holdingKernel_nonneg
  intro x y
  exact axial_holdingKernel_closed_domination c _ _ (axial_fold_preferred c x) (axial_fold_preferred c y)

theorem diagonal_preferred_side (x : Vertex) :
    x.swap.1 < x.swap.2 ↔ ¬x.1 < x.2 ∧ x.swap ≠ x := by
  have heq : x.swap = x ↔ x.1 = x.2 := by
    rcases x with ⟨a, b⟩
    simp only [Prod.swap_prod_mk, Prod.mk.injEq]
    omega
  change x.2 < x.1 ↔ _
  rw [ne_eq, heq]
  omega

theorem diagonal_adjacencyKernel_closed_domination (x y : Vertex)
    (hx : x.1 ≤ x.2) (hy : y.1 ≤ y.2) :
    adjacencyKernel x y.swap ≤ adjacencyKernel x y := by
  by_cases hx0 : x.1 = x.2
  · have hfix : x.swap = x := Prod.ext hx0.symm hx0
    exact le_of_eq (by simpa only [hfix] using diagonal_adjacencyKernel_invariant x y)
  · by_cases hy0 : y.1 = y.2
    · have hfix : y.swap = y := Prod.ext hy0.symm hy0
      rw [hfix]
    · exact diagonal_adjacencyKernel_domination x y (by omega) (by omega)

theorem diagonal_fold_preferred (x : Vertex) :
    (foldToPreferred Prod.swap (fun y : Vertex => y.1 < y.2) x).1 ≤
      (foldToPreferred Prod.swap (fun y : Vertex => y.1 < y.2) x).2 := by
  classical
  unfold foldToPreferred
  split_ifs <;> (try dsimp) <;> omega

/-- Ordinary closed-walk moment comparison for diagonal polarization, with
fixed-axis vertices included. -/
theorem diagonal_adjacency_moments (U : Domain) (n : ℕ) :
    Matrix.trace (domainKernel adjacencyKernel U ^ n) ≤
      Matrix.trace (domainKernel adjacencyKernel
        (polarized U Prod.swap (fun x : Vertex => x.1 < x.2)) ^ n) := by
  apply domainKernel_polarization_moments U Prod.swap (fun x : Vertex => x.1 < x.2)
    Prod.swap_swap diagonal_preferred_side adjacencyKernel
    diagonal_adjacencyKernel_invariant adjacencyKernel_nonneg
  intro x y
  exact diagonal_adjacencyKernel_closed_domination _ _ (diagonal_fold_preferred x) (diagonal_fold_preferred y)

end SpanningTreeIsoperimetry.Polarization







