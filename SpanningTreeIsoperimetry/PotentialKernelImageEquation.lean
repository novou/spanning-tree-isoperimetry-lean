import SpanningTreeIsoperimetry.PotentialKernelHarmonic
import SpanningTreeIsoperimetry.BoundaryGreenLoss

/-! The four-image potential satisfies the actual killed-quadrant Poisson
equation. This is a discrete consequence of the checked integral potential's
full-plane recurrence; no image identification is assumed. -/
namespace SpanningTreeIsoperimetry.PotentialKernelImageEquation
open PotentialKernelIntegral PotentialKernelHarmonic Ferrers BoundaryGreenLoss
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev LatticePoint := ℤ × ℤ

def wholePotential (p : LatticePoint) : ℝ := potential p.1.natAbs p.2.natAbs

def wholeLaplacian (f : LatticePoint → ℝ) (p : LatticePoint) : ℝ :=
  4*f p-f (p.1+1,p.2)-f (p.1-1,p.2)-f (p.1,p.2+1)-f (p.1,p.2-1)

theorem natAbs_neighbor_sum (f : ℕ → ℝ) (x : ℤ) :
    f (x+1).natAbs+f (x-1).natAbs=f (x.natAbs+1)+f (previous x.natAbs) := by
  rcases lt_trichotomy x 0 with hx|hx|hx
  · have ha := Int.ofNat_natAbs_of_nonpos (show x≤0 by omega)
    have hb := Int.ofNat_natAbs_of_nonpos (show x+1≤0 by omega)
    have hc := Int.ofNat_natAbs_of_nonpos (show x-1≤0 by omega)
    have h0 : x.natAbs≠0 := by omega
    have h1 : (x+1).natAbs=x.natAbs-1 := by omega
    have h2 : (x-1).natAbs=x.natAbs+1 := by omega
    rw [h1,h2,previous,if_neg h0,add_comm]
  · subst x
    norm_num [previous]
  · have ha := Int.natAbs_of_nonneg (show 0≤x by omega)
    have hb := Int.natAbs_of_nonneg (show 0≤x+1 by omega)
    have hc := Int.natAbs_of_nonneg (show 0≤x-1 by omega)
    have h0 : x.natAbs≠0 := by omega
    have h1 : (x+1).natAbs=x.natAbs+1 := by omega
    have h2 : (x-1).natAbs=x.natAbs-1 := by omega
    rw [h1,h2,previous,if_neg h0]

theorem wholePotential_poisson (p : LatticePoint) :
    wholeLaplacian wholePotential p=if p=(0,0) then -4 else 0 := by
  have hx := natAbs_neighbor_sum (fun k => potential k p.2.natAbs) p.1
  have hy := natAbs_neighbor_sum (fun k => potential p.1.natAbs k) p.2
  have h := potential_poisson p.1.natAbs p.2.natAbs
  have hz : (p.1.natAbs=0 ∧ p.2.natAbs=0) ↔ p=(0,0) := by
    simp only [Int.natAbs_eq_zero,Prod.ext_iff]
  simp only [hz] at h
  unfold wholeLaplacian wholePotential
  dsimp only [Prod.fst,Prod.snd]
  by_cases hp : p=(0,0) <;> simp only [hp,ite_true,ite_false] at h hx hy ⊢ <;> linarith only [h,hx,hy]

def translatePotential (q p : LatticePoint) : ℝ := wholePotential (p.1-q.1,p.2-q.2)

theorem translatePotential_poisson (q p : LatticePoint) :
    wholeLaplacian (translatePotential q) p=if p=q then -4 else 0 := by
  have he : wholeLaplacian (translatePotential q) p=
      wholeLaplacian wholePotential (p.1-q.1,p.2-q.2) := by
    unfold wholeLaplacian translatePotential
    have hxp : p.1+1-q.1=(p.1-q.1)+1 := by ring
    have hxm : p.1-1-q.1=(p.1-q.1)-1 := by ring
    have hyp : p.2+1-q.2=(p.2-q.2)+1 := by ring
    have hym : p.2-1-q.2=(p.2-q.2)-1 := by ring
    simp only [Prod.fst,Prod.snd,hxp,hxm,hyp,hym]
  rw [he,wholePotential_poisson]
  have hz : (p.1-q.1,p.2-q.2)=(0,0) ↔ p=q := by
    simp only [Prod.mk.injEq,sub_eq_zero,Prod.ext_iff]
  simp only [hz]

def embed (p : Point) : LatticePoint := (p.1,p.2)
def reflectedX (q : Point) : LatticePoint := (-(q.1 : ℤ)-2,q.2)
def reflectedY (q : Point) : LatticePoint := (q.1,-(q.2 : ℤ)-2)
def reflectedXY (q : Point) : LatticePoint := (-(q.1 : ℤ)-2,-(q.2 : ℤ)-2)

def imageZ (q : Point) (p : LatticePoint) : ℝ :=
  (-translatePotential (embed q) p+translatePotential (reflectedX q) p+
    translatePotential (reflectedY q) p-translatePotential (reflectedXY q) p)/4

def image (p q : Point) : ℝ := imageZ q (embed p)

theorem embed_injective : Function.Injective embed := by
  intro p q h
  apply Prod.ext
  · have hx := congrArg Prod.fst h
    dsimp [embed] at hx
    exact_mod_cast hx
  · have hy := congrArg Prod.snd h
    dsimp [embed] at hy
    exact_mod_cast hy

theorem imageZ_poisson_at_embed (p q : Point) :
    wholeLaplacian (imageZ q) (embed p)=if p=q then 1 else 0 := by
  have hlin : wholeLaplacian (imageZ q) (embed p)=
      (-wholeLaplacian (translatePotential (embed q)) (embed p)+
        wholeLaplacian (translatePotential (reflectedX q)) (embed p)+
        wholeLaplacian (translatePotential (reflectedY q)) (embed p)-
        wholeLaplacian (translatePotential (reflectedXY q)) (embed p))/4 := by
    unfold wholeLaplacian imageZ
    ring
  have hx : embed p≠reflectedX q := by
    intro h
    have he := congrArg Prod.fst h
    dsimp [embed,reflectedX] at he
    omega
  have hy : embed p≠reflectedY q := by
    intro h
    have he := congrArg Prod.snd h
    dsimp [embed,reflectedY] at he
    omega
  have hxy : embed p≠reflectedXY q := by
    intro h
    have he := congrArg Prod.fst h
    dsimp [embed,reflectedXY] at he
    omega
  rw [hlin]
  simp only [translatePotential_poisson,hx,hy,hxy,ite_false,embed_injective.eq_iff]
  split_ifs <;> norm_num

theorem imageZ_killed_x (q : Point) (y : ℤ) : imageZ q (-1,y)=0 := by
  have he : (-1-(q.1 : ℤ)).natAbs=(-1-(-(q.1 : ℤ)-2)).natAbs := by
    have h : -1-(q.1 : ℤ)= -(-1-(-(q.1 : ℤ)-2)) := by ring
    rw [h,Int.natAbs_neg]
  unfold imageZ translatePotential wholePotential embed reflectedX reflectedY reflectedXY
  simp only [Prod.fst,Prod.snd,he]
  ring

theorem imageZ_killed_y (q : Point) (x : ℤ) : imageZ q (x,-1)=0 := by
  have he : (-1-(q.2 : ℤ)).natAbs=(-1-(-(q.2 : ℤ)-2)).natAbs := by
    have h : -1-(q.2 : ℤ)= -(-1-(-(q.2 : ℤ)-2)) := by ring
    rw [h,Int.natAbs_neg]
  unfold imageZ translatePotential wholePotential embed reflectedX reflectedY reflectedXY
  simp only [Prod.fst,Prod.snd,he]
  ring

theorem image_west (p q : Point) :
    (if p.1=0 then (0 : ℝ) else image (p.1-1,p.2) q)=imageZ q ((p.1 : ℤ)-1,p.2) := by
  by_cases hp : p.1=0
  · simp only [hp,ite_true,Nat.cast_zero,zero_sub]
    exact (imageZ_killed_x q (p.2 : ℤ)).symm
  · simp only [hp,ite_false,image,embed,Prod.fst,Prod.snd,Nat.cast_sub (by omega : 1≤p.1),Nat.cast_one]

theorem image_south (p q : Point) :
    (if p.2=0 then (0 : ℝ) else image (p.1,p.2-1) q)=imageZ q (p.1,(p.2 : ℤ)-1) := by
  by_cases hp : p.2=0
  · simp only [hp,ite_true,Nat.cast_zero,zero_sub]
    exact (imageZ_killed_y q (p.1 : ℤ)).symm
  · simp only [hp,ite_false,image,embed,Prod.fst,Prod.snd,Nat.cast_sub (by omega : 1≤p.2),Nat.cast_one]

theorem image_poisson (p q : Point) :
    laplacian (fun t => image t q) p=if p=q then 1 else 0 := by
  rw [laplacian,image_west,image_south]
  have he : 4*image p q-image (p.1+1,p.2) q-imageZ q ((p.1 : ℤ)-1,p.2)-
      image (p.1,p.2+1) q-imageZ q (p.1,(p.2 : ℤ)-1)=wholeLaplacian (imageZ q) (embed p) := by
    simp only [image,wholeLaplacian,embed,Prod.fst,Prod.snd,Nat.cast_add,Nat.cast_one]
  rw [he,imageZ_poisson_at_embed]

theorem natAbs_nat_sub (a b : ℕ) : ((a : ℤ)-b).natAbs=Nat.dist a b := by
  by_cases hab : a≤b
  · have h := Int.ofNat_natAbs_of_nonpos (show (a : ℤ)-b≤0 by omega)
    rw [Nat.dist_eq_sub_of_le hab]
    omega
  · have h := Int.natAbs_of_nonneg (show 0≤(a : ℤ)-b by omega)
    rw [Nat.dist_eq_sub_of_le_right (by omega : b≤a)]
    omega

theorem natAbs_reflected (a b : ℕ) : ((a : ℤ)-(-(b : ℤ)-2)).natAbs=a+b+2 := by
  have he : (a : ℤ)-(-(b : ℤ)-2)=((a+b+2 : ℕ) : ℤ) := by push_cast; ring
  rw [he,Int.natAbs_natCast]

/-- Literal four-image expression in the manuscript's nonnegative
coordinates; adding one to each site gives its positive-face convention. -/
theorem image_formula (p q : Point) : image p q=
    (-potential (Nat.dist p.1 q.1) (Nat.dist p.2 q.2)+
      potential (p.1+q.1+2) (Nat.dist p.2 q.2)+
      potential (Nat.dist p.1 q.1) (p.2+q.2+2)-
      potential (p.1+q.1+2) (p.2+q.2+2))/4 := by
  unfold image imageZ translatePotential wholePotential embed reflectedX reflectedY reflectedXY
  simp only [Prod.fst,Prod.snd,natAbs_nat_sub,natAbs_reflected]

end
end SpanningTreeIsoperimetry.PotentialKernelImageEquation
