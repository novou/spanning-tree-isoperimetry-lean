import SpanningTreeIsoperimetry.BoundaryHalfPlane

/-! Additional exact boundary Green sums at displacements six through eight.
The polynomial candidates are checked by rational identities in Lean. -/
namespace SpanningTreeIsoperimetry.BoundaryGreenExtension
open BoundaryGreen Filter Polynomial
open scoped BigOperators Topology
noncomputable section

def extraNumerator (i : Fin 3) : Polynomial ℝ :=
  ![C 182995200 + C (58131165105/56) * X^1 + C (272751048621/112) * X^2 + C (3603205735779/1120) * X^3 + C (6064924247091/2240) * X^4 + C (2594415335843/1680) * X^5 + C (4140891717469/6720) * X^6 + C (1219207991/7) * X^7 + C (3891260455/112) * X^8 + C (167460029/35) * X^9 + C (60601837/140) * X^10 + C (2430784/105) * X^11 + C (58223/105) * X^12,
    C 42877900800 + C (8175344813685/32) * X^1 + C (20511446113575/32) * X^2 + C (4129715165598447/4480) * X^3 + C (1929608811453443/2240) * X^4 + C (1251018803583039/2240) * X^5 + C (292001326603701/1120) * X^6 + C (400725729060491/4480) * X^7 + C (50954498691029/2240) * X^8 + C (4793464099071/1120) * X^9 + C (329208005089/560) * X^10 + C (16039027857/280) * X^11 + C (524950383/140) * X^12 + C (10347517/70) * X^13 + C (92803/35) * X^14,
    C 13423424716800 + C (666693504382815/8) * X^1 + C (14135809461294615/64) * X^2 + C (761600530572049551/2240) * X^3 + C (9272600369088502079/26880) * X^4 + C (248745599595993709/1008) * X^5 + C (1044644928627052621/8064) * X^6 + C (1030973291310435833/20160) * X^7 + C (177377531738756827/11520) * X^8 + C (3586214310789127/1008) * X^9 + C (635320109197961/1008) * X^10 + C (106946581115377/1260) * X^11 + C (21502423640923/2520) * X^12 + C (39056558189/63) * X^13 + C (276669781/9) * X^14 + C (41877112/45) * X^15 + C (4085573/315) * X^16] i

def extraDenominator (i : Fin 3) : Polynomial ℝ :=
  ∏ l ∈ Finset.range (6+i.val), (X+C (l+1 : ℝ))^2

def extraInitial (i : Fin 3) : ℝ := ![353,1688,8257] i

def extraLimit (i : Fin 3) : ℝ := ![58223/105,92803/35,4085573/315] i

def extraTelescoper (i : Fin 3) (m : ℕ) : ℝ :=
  (extraNumerator i).eval (m : ℝ)/(extraDenominator i).eval (m : ℝ)

def extraCoefficient (i : Fin 3) (m : ℕ) : ℝ :=
  wallisReciprocal m*(∏ l ∈ Finset.range (6+i.val), (2*(m : ℝ)+l+1)^2)*
    (2*m+(6+i.val)+1)/
    ((∏ l ∈ Finset.range (6+i.val), ((m : ℝ)+l+1)^2)*
      (2*m+1)*4^(6+i.val+1)*(m+1)*(m+(6+i.val)+1))

theorem extraCoefficient_nonneg (i : Fin 3) (m : ℕ) : 0≤extraCoefficient i m := by
  unfold extraCoefficient
  have hb := (wallisReciprocal_pos m).le
  positivity

theorem extraNumerator_degree (i : Fin 3) : (extraNumerator i).degree=(2*(6+i.val) : ℕ) := by
  fin_cases i <;> norm_num [extraNumerator] <;> compute_degree!

theorem extraDenominator_degree (i : Fin 3) : (extraDenominator i).degree=(2*(6+i.val) : ℕ) := by
  fin_cases i <;> simp only [extraDenominator, Finset.prod_range_succ,Finset.prod_range_zero] <;>
    compute_degree!

theorem extraNumerator_leadingCoeff (i : Fin 3) :
    (extraNumerator i).leadingCoeff=extraLimit i := by
  rw [Polynomial.leadingCoeff,Polynomial.natDegree_eq_of_degree_eq_some (extraNumerator_degree i)]
  fin_cases i <;> norm_num [extraNumerator,extraLimit] <;> compute_degree!

theorem extraDenominator_leadingCoeff (i : Fin 3) : (extraDenominator i).leadingCoeff=1 := by
  unfold extraDenominator
  exact monic_prod_of_monic _ _ (fun l _ => (monic_X_add_C (l+1 : ℝ)).pow 2)

theorem extraTelescoper_tendsto (i : Fin 3) :
    Tendsto (extraTelescoper i) atTop (𝓝 (extraLimit i)) := by
  have hd : (extraNumerator i).degree=(extraDenominator i).degree := by
    rw [extraNumerator_degree,extraDenominator_degree]
  have h := (Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
    (extraNumerator i) (extraDenominator i) hd).comp tendsto_natCast_atTop_atTop
  change Tendsto (fun m : ℕ => (extraNumerator i).eval (m : ℝ)/
    (extraDenominator i).eval (m : ℝ)) atTop (𝓝 (extraLimit i))
  simpa only [Function.comp_def,extraNumerator_leadingCoeff,extraDenominator_leadingCoeff,div_one] using h

theorem extraTelescoper_initial (i : Fin 3) : extraTelescoper i 0=extraInitial i := by
  fin_cases i <;> norm_num [extraTelescoper,extraNumerator,extraDenominator,extraInitial,
    Finset.prod_range_succ,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow]

set_option maxHeartbeats 4000000 in
 theorem extraCoefficient_telescope (i : Fin 3) (m : ℕ) :
    extraCoefficient i m=wallisReciprocal (m+1)*extraTelescoper i (m+1)-
      wallisReciprocal m*extraTelescoper i m := by
  rw [wallisReciprocal_succ]
  fin_cases i <;>
    norm_num [extraCoefficient,extraTelescoper,extraNumerator,extraDenominator,
      Finset.prod_range_succ,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow] <;>
    field_simp <;> ring

theorem extraCoefficient_hasSum (i : Fin 3) :
    HasSum (extraCoefficient i) (2/Real.pi*extraLimit i-extraInitial i) := by
  have h := hasSum_of_wallis_telescope (extraCoefficient i) (extraTelescoper i) (extraLimit i)
    (extraCoefficient_nonneg i) (extraCoefficient_telescope i) (extraTelescoper_tendsto i)
  simpa only [extraTelescoper_initial] using h

theorem halfPlaneCoefficient_extra_shift (i : Fin 3) (m : ℕ) :
    halfPlaneCoefficient (2*m+(6+i.val)) (6+i.val)=extraCoefficient i m := by
  unfold halfPlaneCoefficient
  rw [halfPlane_count_real,shifted_choose_ratio]
  unfold extraCoefficient
  rw [wallisReciprocal_eq_central]
  unfold SpanningTreeIsoperimetry.CornerEnergy.normalizedCentralBinom
  simp only [Finset.prod_pow]
  have hd : (∏ l ∈ Finset.range (6+i.val), ((m : ℝ)+l+1))≠0 :=
    (Finset.prod_pos (fun l _ => by positivity)).ne'
  have hp : (4 : ℝ)^(2*m+(6+i.val)+1)=(4^m)^2*4^(6+i.val+1) := by
    rw [show 2*m+(6+i.val)+1=m*2+(6+i.val+1) by omega,pow_add,pow_mul]
  rw [hp]
  push_cast
  field_simp [hd]
  <;> ring

def extraValue (i : Fin 3) : ℝ := 2/Real.pi*extraLimit i-extraInitial i

theorem halfPlaneCoefficient_extra_hasSum (i : Fin 3) :
    HasSum (fun n => halfPlaneCoefficient n (6+i.val)) (extraValue i) := by
  have heven : HasSum (fun m => halfPlaneCoefficient (2*m+(6+i.val)) (6+i.val)) (extraValue i) :=
    (extraCoefficient_hasSum i).congr_fun (fun m => halfPlaneCoefficient_extra_shift i m)
  have hodd : HasSum (fun m => halfPlaneCoefficient (2*m+1+(6+i.val)) (6+i.val)) (0 : ℝ) := by
    simp [halfPlaneCoefficient,halfPlane_count_wrongParity]
  have hshift : HasSum (fun n => halfPlaneCoefficient (n+(6+i.val)) (6+i.val)) (extraValue i) := by
    simpa only [add_zero] using heven.even_add_odd
      (f := fun n => halfPlaneCoefficient (n+(6+i.val)) (6+i.val)) hodd
  have hprefix : ∑ n ∈ Finset.range (6+i.val), halfPlaneCoefficient n (6+i.val)=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [halfPlaneCoefficient,halfPlane_count_short (Finset.mem_range.mp hn),Nat.cast_zero,zero_div]
  simpa only [hprefix,zero_add] using hshift.sum_range_add
    (f := fun n => halfPlaneCoefficient n (6+i.val)) (k := 6+i.val)

def boundaryValueNine (j : Fin 9) : ℝ :=
  if h : j.val<6 then boundaryValue ⟨j.val,h⟩ else extraValue ⟨j.val-6,by omega⟩

theorem halfPlaneCoefficient_nine_hasSum (j : Fin 9) :
    HasSum (fun n => halfPlaneCoefficient n j.val) (boundaryValueNine j) := by
  unfold boundaryValueNine
  split_ifs with h
  · exact halfPlaneCoefficient_hasSum ⟨j.val,h⟩
  · have hi : 6+(j.val-6)=j.val := by omega
    simpa only [hi] using halfPlaneCoefficient_extra_hasSum ⟨j.val-6,by omega⟩

end
end SpanningTreeIsoperimetry.BoundaryGreenExtension
