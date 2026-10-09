import SpanningTreeIsoperimetry.EnergyConvergence
import SpanningTreeIsoperimetry.CornerEnergySymmetry

/-! Two maximal cells give exactly the two-tier diagrams used in the refined
corner envelope. Increasing a tier parameter is row or column repetition. -/
namespace SpanningTreeIsoperimetry.TwoTierFerrers
open Ferrers CornerEnergy
open scoped Classical

def twoTier (b c p q : ℕ) : Diagram :=
  faceRectangle (b+c) p ∪ faceRectangle b (p+q)

@[simp] theorem mem_twoTier {b c p q : ℕ} {z : Point} :
    z∈twoTier b c p q ↔ (z.1<b+c ∧ z.2<p) ∨ (z.1<b ∧ z.2<p+q) := by
  simp only [twoTier,Finset.mem_union,mem_faceRectangle]

theorem twoTier_isFerrers (b c p q : ℕ) : IsFerrers (twoTier b c p q) := by
  intro z hz w hx hy
  simp only [mem_twoTier] at hz ⊢
  rcases hz with hz|hz
  · exact Or.inl ⟨lt_of_le_of_lt hx hz.1,lt_of_le_of_lt hy hz.2⟩
  · exact Or.inr ⟨lt_of_le_of_lt hx hz.1,lt_of_le_of_lt hy hz.2⟩

private theorem twoTier_of_ordered_maxima {M : Diagram} (hM : IsFerrers M)
    {u v : Point} (hu : u∈maximalCells M) (hv : v∈maximalCells M)
    (hne : u≠v) (hcover : maximalCells M={u,v}) (hxu : u.1≤v.1) :
    ∃ b c p q, 0<b ∧ 0<c ∧ 0<p ∧ 0<q ∧ M=twoTier b c p q := by
  have hy : v.2<u.2 := by
    by_contra hn
    have he := (mem_maximalCells.mp hu).2 v (mem_maximalCells.mp hv).1 hxu (by omega)
    exact hne he.symm
  have hx : u.1<v.1 := by
    by_contra hn
    have he := (mem_maximalCells.mp hv).2 u (mem_maximalCells.mp hu).1 (by omega) hy.le
    exact hne he
  refine ⟨u.1+1,v.1-u.1,v.2+1,u.2-v.2,by omega,by omega,by omega,by omega,?_⟩
  ext z
  simp only [mem_twoTier]
  constructor
  · intro hz
    obtain ⟨w,hw,hzw⟩ := exists_dominating_maximal hz
    rw [hcover] at hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl|rfl
    · right
      constructor <;> omega
    · left
      constructor <;> omega
  · rintro (hz|hz)
    · exact hM v (mem_maximalCells.mp hv).1 z (by omega) (by omega)
    · exact hM u (mem_maximalCells.mp hu).1 z (by omega) (by omega)

theorem exists_twoTier_of_two_maxima {M : Diagram} (hM : IsFerrers M)
    (hc : (maximalCells M).card=2) :
    ∃ b c p q, 0<b ∧ 0<c ∧ 0<p ∧ 0<q ∧ M=twoTier b c p q := by
  obtain ⟨u,v,hne,hcover⟩ := Finset.card_eq_two.mp hc
  have hu : u∈maximalCells M := by rw [hcover]; simp
  have hv : v∈maximalCells M := by rw [hcover]; simp
  rcases le_total u.1 v.1 with h|h
  · exact twoTier_of_ordered_maxima hM hu hv hne hcover h
  · exact twoTier_of_ordered_maxima hM hv hu hne.symm
      (by simpa only [Finset.pair_comm] using hcover) h

theorem duplicate_first_row (b c p q : ℕ) (hp : 0<p) :
    duplicateRow (twoTier b c p q) 0=twoTier b c (p+1) q := by
  ext z
  rw [mem_duplicateRow_iff (twoTier_isFerrers b c p q)]
  simp only [mem_twoTier]
  split_ifs <;> omega

theorem duplicate_last_row (b c p q : ℕ) (hq : 0<q) :
    duplicateRow (twoTier b c p q) (p+q-1)=twoTier b c p (q+1) := by
  ext z
  rw [mem_duplicateRow_iff (twoTier_isFerrers b c p q)]
  simp only [mem_twoTier]
  split_ifs <;> omega

theorem energy_succ_p (b c p q : ℕ) (hp : 0<p) :
    realEnergy (twoTier b c p q)≤realEnergy (twoTier b c (p+1) q) := by
  rw [← duplicate_first_row b c p q hp]
  exact realEnergy_duplicateRow (twoTier_isFerrers b c p q) 0

theorem energy_succ_q (b c p q : ℕ) (hq : 0<q) :
    realEnergy (twoTier b c p q)≤realEnergy (twoTier b c p (q+1)) := by
  rw [← duplicate_last_row b c p q hq]
  exact realEnergy_duplicateRow (twoTier_isFerrers b c p q) (p+q-1)

theorem transpose_twoTier (b c p q : ℕ) :
    transpose (twoTier b c p q)=twoTier p q b c := by
  ext z
  simp only [mem_transpose,mem_twoTier,Prod.fst_swap,Prod.snd_swap]
  omega

theorem energy_succ_b (b c p q : ℕ) (hb : 0<b) :
    realEnergy (twoTier b c p q)≤realEnergy (twoTier (b+1) c p q) := by
  have hh := energy_succ_p p q b c hb
  rw [← transpose_twoTier b c p q,← transpose_twoTier (b+1) c p q,
    realEnergy_transpose,realEnergy_transpose] at hh
  exact hh

theorem energy_succ_c (b c p q : ℕ) (hc : 0<c) :
    realEnergy (twoTier b c p q)≤realEnergy (twoTier b (c+1) p q) := by
  have hh := energy_succ_q p q b c hc
  rw [← transpose_twoTier b c p q,← transpose_twoTier b (c+1) p q,
    realEnergy_transpose,realEnergy_transpose] at hh
  exact hh

theorem energy_mono_p {b c p q P : ℕ} (hp : 0<p) (h : p≤P) :
    realEnergy (twoTier b c p q)≤realEnergy (twoTier b c P q) := by
  induction P,h using Nat.le_induction with
  | base => rfl
  | succ P h ih => exact ih.trans (energy_succ_p b c P q (by omega))

theorem energy_mono_q {b c p q Q : ℕ} (hq : 0<q) (h : q≤Q) :
    realEnergy (twoTier b c p q)≤realEnergy (twoTier b c p Q) := by
  induction Q,h using Nat.le_induction with
  | base => rfl
  | succ Q h ih => exact ih.trans (energy_succ_q b c p Q (by omega))

theorem energy_mono_b {b c p q B : ℕ} (hb : 0<b) (h : b≤B) :
    realEnergy (twoTier b c p q)≤realEnergy (twoTier B c p q) := by
  induction B,h using Nat.le_induction with
  | base => rfl
  | succ B h ih => exact ih.trans (energy_succ_b B c p q (by omega))

theorem energy_mono_c {b c p q C : ℕ} (hc : 0<c) (h : c≤C) :
    realEnergy (twoTier b c p q)≤realEnergy (twoTier b C p q) := by
  induction C,h using Nat.le_induction with
  | base => rfl
  | succ C h ih => exact ih.trans (energy_succ_c b C p q (by omega))

theorem energy_mono {b c p q B C P Q : ℕ}
    (hb : 0<b) (hc : 0<c) (hp : 0<p) (hq : 0<q)
    (hbB : b≤B) (hcC : c≤C) (hpP : p≤P) (hqQ : q≤Q) :
    realEnergy (twoTier b c p q)≤realEnergy (twoTier B C P Q) :=
  (energy_mono_b hb hbB).trans ((energy_mono_c hc hcC).trans
    ((energy_mono_p hp hpP).trans (energy_mono_q hq hqQ)))

theorem twoTier_card (b c p q : ℕ) : (twoTier b c p q).card=(b+c)*p+b*q := by
  have hi : faceRectangle (b+c) p ∩ faceRectangle b (p+q)=faceRectangle b p := by
    ext z
    simp only [Finset.mem_inter,mem_faceRectangle]
    omega
  have hh := Finset.card_union_add_card_inter (faceRectangle (b+c) p) (faceRectangle b (p+q))
  rw [hi] at hh
  change (twoTier b c p q).card+(faceRectangle b p).card=
    (faceRectangle (b+c) p).card+(faceRectangle b (p+q)).card at hh
  simp only [faceRectangle,Finset.card_product,Finset.card_range] at hh
  nlinarith

/-- Every two-tier diagram of size at least five is obtained, in the energy
order, from (3,2), (4,1), (3,1,1), or their transposes. -/
theorem twoTier_large_seed_bound {b c p q : ℕ}
    (hb : 0<b) (hc : 0<c) (hp : 0<p) (hq : 0<q)
    (hsize : 5≤(twoTier b c p q).card) :
    realEnergy (twoTier 2 1 1 1)≤realEnergy (twoTier b c p q) ∨
      realEnergy (twoTier 1 3 1 1)≤realEnergy (twoTier b c p q) ∨
        realEnergy (twoTier 1 2 1 2)≤realEnergy (twoTier b c p q) := by
  by_cases hb2 : 2≤b
  · exact Or.inl (energy_mono (by omega) (by omega) (by omega) (by omega)
      hb2 (by omega) (by omega) (by omega))
  by_cases hp2 : 2≤p
  · have hh : realEnergy (twoTier 1 1 2 1)≤realEnergy (twoTier b c p q) :=
      energy_mono (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) hp2 (by omega)
    rw [← transpose_twoTier 2 1 1 1,realEnergy_transpose] at hh
    exact Or.inl hh
  by_cases hc3 : 3≤c
  · exact Or.inr (Or.inl (energy_mono (by omega) (by omega) (by omega) (by omega)
      (by omega) hc3 (by omega) (by omega)))
  by_cases hq3 : 3≤q
  · have hh : realEnergy (twoTier 1 1 1 3)≤realEnergy (twoTier b c p q) :=
      energy_mono (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) hq3
    rw [← transpose_twoTier 1 3 1 1,realEnergy_transpose] at hh
    exact Or.inr (Or.inl hh)
  · have hb1 : b=1 := by omega
    have hp1 : p=1 := by omega
    rw [twoTier_card,hb1,hp1] at hsize
    have hc2 : c=2 := by omega
    have hq2 : q=2 := by omega
    subst b; subst c; subst p; subst q
    exact Or.inr (Or.inr le_rfl)

theorem two_maxima_large_seed_bound {M : Diagram} (hM : IsFerrers M)
    (hc : (maximalCells M).card=2) (hsize : 5≤M.card) :
    realEnergy (twoTier 2 1 1 1)≤realEnergy M ∨
      realEnergy (twoTier 1 3 1 1)≤realEnergy M ∨
        realEnergy (twoTier 1 2 1 2)≤realEnergy M := by
  obtain ⟨b,c,p,q,hb,hcpos,hp,hq,rfl⟩ := exists_twoTier_of_two_maxima hM hc
  exact twoTier_large_seed_bound hb hcpos hp hq hsize

end SpanningTreeIsoperimetry.TwoTierFerrers
