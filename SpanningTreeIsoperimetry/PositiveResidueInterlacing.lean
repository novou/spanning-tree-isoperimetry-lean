module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

/-! A finite positive-residue rational function has a numerator whose roots
strictly alternate with its ordered poles. The proof is included locally:
consecutive endpoint signs, the intermediate value theorem, and polynomial
divisibility/degree. No interlacing theorem is assumed. -/
namespace SpanningTreeIsoperimetry.PositiveResidueInterlacing
open Polynomial Set
open scoped BigOperators Classical
noncomputable section

def numerator {w : ℕ} (pole weight : Fin w → ℝ) : Polynomial ℝ :=
  ∑ i : Fin w,C (weight i)*(∏ j ∈ Finset.univ.erase i,(X-C (pole j)))

def leftIndex {w : ℕ} (hw : 0<w) (i : Fin (w-1)) : Fin w := ⟨i.val,by have h:=i.isLt; omega⟩
def rightIndex {w : ℕ} (hw : 0<w) (i : Fin (w-1)) : Fin w := ⟨i.val+1,by have h:=i.isLt; omega⟩

theorem eval_at_pole {w : ℕ} (pole weight : Fin w → ℝ)
    (hinj : Function.Injective pole) (i : Fin w) :
    (numerator pole weight).eval (pole i)=weight i*(∏ j ∈ Finset.univ.erase i,(pole i-pole j)) := by
  simp only [numerator,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X]
  apply Finset.sum_eq_single i
  · intro j _ hji
    have hi : i∈Finset.univ.erase j := Finset.mem_erase.mpr ⟨hji.symm,Finset.mem_univ _⟩
    rw [Finset.prod_eq_zero hi (by simp),mul_zero]
  · simp

/-- The weighted polynomial numerator has the finite partial-fraction
identity away from its explicitly listed poles. -/
theorem eval_div_product {w : ℕ} (pole weight : Fin w → ℝ) (z : ℝ)
    (hz : ∀ i,z≠pole i) :
    (numerator pole weight).eval z/(∏ i : Fin w,(z-pole i))=
      ∑ i : Fin w,weight i/(z-pole i) := by
  rw [numerator,Polynomial.eval_finsetSum]
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_prod,
    Polynomial.eval_sub,Polynomial.eval_X]
  have hprod : (∏ j ∈ Finset.univ.erase i,(z-pole j))≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => sub_ne_zero.mpr (hz j))
  have he : (∏ j : Fin w,(z-pole j))=
      (∏ j ∈ Finset.univ.erase i,(z-pole j))*(z-pole i) :=
    (Finset.prod_erase_mul Finset.univ (fun j => z-pole j) (Finset.mem_univ i)).symm
  rw [he]
  field_simp [hprod,sub_ne_zero.mpr (hz i)]
  <;> ring

theorem eval_at_pole_ne_zero {w : ℕ} (pole weight : Fin w → ℝ)
    (hinj : Function.Injective pole) (hwgt : ∀ i,0<weight i) (i : Fin w) :
    (numerator pole weight).eval (pole i)≠0 := by
  rw [eval_at_pole pole weight hinj]
  apply mul_ne_zero (hwgt i).ne'
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr (hinj.ne (Finset.ne_of_mem_erase hj).symm)

theorem numerator_natDegree_le {w : ℕ} (pole weight : Fin w → ℝ) :
    (numerator pole weight).natDegree≤w-1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  simp only [natDegree_finsetProd_X_sub_C_eq_card,
    Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin,le_refl]

theorem adjacent_sign {w : ℕ} (hw : 0<w) (pole weight : Fin w → ℝ)
    (hpole : StrictMono pole) (hwgt : ∀ i,0<weight i) (i : Fin (w-1)) :
    (numerator pole weight).eval (pole (leftIndex hw i))*
      (numerator pole weight).eval (pole (rightIndex hw i))<0 := by
  let a := leftIndex hw i
  let b := rightIndex hw i
  let S := (Finset.univ.erase a).erase b
  have hab : a<b := by change i.val < i.val + 1; omega
  have hne : a≠b := ne_of_lt hab
  have hp : pole a<pole b := hpole hab
  have hba : b∈Finset.univ.erase a := Finset.mem_erase.mpr ⟨hne.symm,Finset.mem_univ _⟩
  have hab' : a∈Finset.univ.erase b := Finset.mem_erase.mpr ⟨hne,Finset.mem_univ _⟩
  have hpa : (∏ j ∈ Finset.univ.erase a,(pole a-pole j))=
      (pole a-pole b)*(∏ j ∈ S,(pole a-pole j)) :=
    (Finset.mul_prod_erase (Finset.univ.erase a) (fun j => pole a-pole j) hba).symm
  have hpb : (∏ j ∈ Finset.univ.erase b,(pole b-pole j))=
      (pole b-pole a)*(∏ j ∈ S,(pole b-pole j)) := by
    have h := (Finset.mul_prod_erase (Finset.univ.erase b) (fun j => pole b-pole j) hab').symm
    simpa only [Finset.erase_right_comm,S] using h
  have hprod : 0<(∏ j ∈ S,(pole a-pole j))*(∏ j ∈ S,(pole b-pole j)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_pos
    intro j hj
    have hja : j≠a := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    have hjb : j≠b := (Finset.mem_erase.mp hj).1
    have hcases : j<a ∨ b<j := by
      have ha : a.val=i.val := rfl
      have hb : b.val=i.val+1 := rfl
      have hja' : j.val≠a.val := fun h => hja (Fin.ext h)
      have hjb' : j.val≠b.val := fun h => hjb (Fin.ext h)
      change j.val<a.val ∨ b.val<j.val
      omega
    rcases hcases with h|h
    · exact mul_pos (sub_pos.mpr (hpole h)) (sub_pos.mpr (hpole (h.trans hab)))
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr (hpole (hab.trans h))) (sub_neg.mpr (hpole h))
  have hgap : (pole a-pole b)*(pole b-pole a)<0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr hp) (sub_pos.mpr hp)
  have hweight : 0<weight a*weight b := mul_pos (hwgt a) (hwgt b)
  rw [eval_at_pole pole weight hpole.injective,eval_at_pole pole weight hpole.injective]
  change (weight a*(∏ j ∈ Finset.univ.erase a,(pole a-pole j)))*
    (weight b*(∏ j ∈ Finset.univ.erase b,(pole b-pole j)))<0
  rw [hpa,hpb]
  have h := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hweight hgap) hprod
  convert h using 1 <;> ring

private theorem root_between {p : Polynomial ℝ} {a b : ℝ} (hab : a<b)
    (hs : p.eval a*p.eval b<0) : ∃ x : ℝ,a<x ∧ x<b ∧ p.eval x=0 := by
  have ha : p.eval a≠0 := by intro h; rw [h,zero_mul] at hs; exact lt_irrefl _ hs
  have hb : p.eval b≠0 := by intro h; rw [h,mul_zero] at hs; exact lt_irrefl _ hs
  have hex : ∃ x : ℝ,x∈Icc a b ∧ p.eval x=0 := by
    rcases mul_neg_iff.mp hs with h|h
    · exact intermediate_value_Icc' hab.le p.continuous.continuousOn ⟨h.2.le,h.1.le⟩
    · exact intermediate_value_Icc hab.le p.continuous.continuousOn ⟨h.1.le,h.2.le⟩
  obtain ⟨x,hx,hroot⟩ := hex
  refine ⟨x,lt_of_le_of_ne hx.1 ?_,lt_of_le_of_ne hx.2 ?_,hroot⟩
  · intro h
    subst x
    exact ha hroot
  · intro h
    subst x
    exact hb hroot

/-- Explicit meaning of strict zero interlacing: one root in every adjacent
pole interval, in increasing order, and a complete polynomial factorization
showing that there are no additional roots. -/
theorem exists_interlacing {w : ℕ} (hw : 0<w) (pole weight : Fin w → ℝ)
    (hpole : StrictMono pole) (hwgt : ∀ i,0<weight i) :
    ∃ root : Fin (w-1) → ℝ, StrictMono root ∧
      (∀ i,pole (leftIndex hw i)<root i ∧ root i<pole (rightIndex hw i)) ∧
      numerator pole weight=(∏ i : Fin (w-1),(X-C (root i)))*
        C (numerator pole weight).leadingCoeff ∧ (numerator pole weight).leadingCoeff≠0 := by
  have hex (i : Fin (w-1)) : ∃ x : ℝ,pole (leftIndex hw i)<x ∧
      x<pole (rightIndex hw i) ∧ (numerator pole weight).eval x=0 :=
    root_between (hpole (by change i.val < i.val + 1; omega)) (adjacent_sign hw pole weight hpole hwgt i)
  choose root hleft hright hroot using hex
  have hmono : StrictMono root := by
    intro i j hij
    have hidx : rightIndex hw i≤leftIndex hw j := by change i.val+1≤j.val; omega
    exact (hright i).trans_le ((hpole.monotone hidx).trans (hleft j).le)
  have hdvd : (∏ i : Fin (w-1),(X-C (root i)))∣numerator pole weight :=
    Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C hmono.injective)
      (fun i => dvd_iff_isRoot.mpr (hroot i))
  have hmon : (∏ i : Fin (w-1),(X-C (root i))).Monic := monic_prod_X_sub_C _ _
  have hfactor := eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le hmon hdvd
    (show (numerator pole weight).natDegree≤(∏ i : Fin (w-1),(X-C (root i))).natDegree by
      simpa only [natDegree_finsetProd_X_sub_C_eq_card,Finset.card_univ,Fintype.card_fin]
        using numerator_natDegree_le pole weight)
  have hn : numerator pole weight≠0 := by
    intro he
    have h := eval_at_pole_ne_zero pole weight hpole.injective hwgt ⟨0,hw⟩
    rw [he,Polynomial.eval_zero] at h
    exact h rfl
  exact ⟨root,hmono,fun i => ⟨hleft i,hright i⟩,hfactor,Polynomial.leadingCoeff_ne_zero.mpr hn⟩

end
end SpanningTreeIsoperimetry.PositiveResidueInterlacing
