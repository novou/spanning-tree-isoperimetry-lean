module

public import SpanningTreeIsoperimetry.BoundaryGreenExtension
public import SpanningTreeIsoperimetry.BoundaryGreenPolynomials

@[expose] public section

/-! Additional exact half-plane Green sums at displacements nine through twelve.
The displayed polynomial candidates are checked by local rational identities. -/
namespace SpanningTreeIsoperimetry.BoundaryGreenRefined
open BoundaryGreen BoundaryGreenExtension Filter Polynomial
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def refinedNumerator (i : Fin 4) : Polynomial ℝ :=
  ![C 5415812952883200 + C (1114448698734583905/32) * X^1 + C (12371409293102050113/128) * X^2 + C (705127053839151522339/4480) * X^3 + C (612012655885574328351/3584) * X^4 + C (2368746024993259921617/17920) * X^5 + C (1022906752502733273989/13440) * X^6 + C (2699550272774404983949/80640) * X^7 + C (369090225535003735859/32256) * X^8 + C (495230836453249375841/161280) * X^9 + C (52413247925549930963/80640) * X^10 + C (1093431705777527687/10080) * X^11 + C (7152768673509815/504) * X^12 + C (7247135150752787/5040) * X^13 + C (278427203864141/2520) * X^14 + C (3918332583901/630) * X^15 + C (30465475837/126) * X^16 + C (3652855537/630) * X^17 + C (20350171/315) * X^18,
    C 2737732425523200000 + C (1597429145039536092375/88) * X^1 + C (9223541529235237802475/176) * X^2 + C (882227196759731787110745/9856) * X^3 + C (2024876504844784256929863/19712) * X^4 + C (1521052837824761643646569/17920) * X^5 + C (12466099006075158345313771/236544) * X^6 + C (2039029979232471872045551/80640) * X^7 + C (16948756773551806148127067/1774080) * X^8 + C (567371883354762350911383/197120) * X^9 + C (54945237950126783444033/78848) * X^10 + C (10058280223408907730371/73920) * X^11 + C (6335475885687741478009/295680) * X^12 + C (150245909144799597809/55440) * X^13 + C (6053376140333464301/22176) * X^14 + C (755413428581902/35) * X^15 + C (4033426365591911/3080) * X^16 + C (12351504845383/210) * X^17 + C (567066669077/308) * X^18 + C (124191703004/3465) * X^19 + C (1131587279/3465) * X^20,
    C 1695217033400647680000 + C (369548818860407242431375/32) * X^1 + C (2208513676300540593736725/64) * X^2 + C (2421383569989579694794457935/39424) * X^3 + C (2915493418878071721454649499/39424) * X^4 + C (7274417009552152895695691853/112640) * X^5 + C (7217026449164779110438431359/168960) * X^6 + C (2029781714366985619420794511/92160) * X^7 + C (4578147016394174562762800141/506880) * X^8 + C (1927116577809134629817578967/645120) * X^9 + C (2854245463729825655565013957/3548160) * X^10 + C (59959771605503627796151649/337920) * X^11 + C (1810842243666175817013773/56320) * X^12 + C (242627933463937046842249/50688) * X^13 + C (14795314091512468684855/25344) * X^14 + C (12854223846980053454993/221760) * X^15 + C (514225425578632980743/110880) * X^16 + C (70632637500287491/240) * X^17 + C (19091529541037971/1320) * X^18 + C (190965774976429/360) * X^19 + C (27045109280009/1980) * X^20 + C (1525870256599/6930) * X^21 + C (5790778969/3465) * X^22,
    C 1262180122251777146880000 + C (1832223701210427193772998125/208) * X^1 + C (22576246189082636516152258725/832) * X^2 + C (987012407643793977565168279515/19712) * X^3 + C (4956501275027008728968956251591/78848) * X^4 + C (2107836692520542983513434864555/36608) * X^5 + C (14983823314956679944476443563861/372736) * X^6 + C (45123378496210219315910181411/2048) * X^7 + C (5669114941749840293385981015295/585728) * X^8 + C (31908439602315210319310436762959/9225216) * X^9 + C (37503546239389232992907875811977/36900864) * X^10 + C (652040747170116856739515636613/2635776) * X^11 + C (1849375824826110117202547957987/36900864) * X^12 + C (1860704421978102748814768959/219648) * X^13 + C (262455914120021841596313455/219648) * X^14 + C (3112400666335541153357479/22176) * X^15 + C (220379357938875825875063/16128) * X^16 + C (2048586424112613540059/1872) * X^17 + C (5136465637140995859259/72072) * X^18 + C (979818346954761275/264) * X^19 + C (1034944182296044721/6864) * X^20 + C (82913163012803023/18018) * X^21 + C (1787243948220407/18018) * X^22 + C (1732103692372/1287) * X^23 + C (77847356975/9009) * X^24] i

def refinedDenominator (i : Fin 4) : Polynomial ℝ :=
  ∏ l ∈ Finset.range (9+i.val), (X+C (l+1 : ℝ))^2

def refinedInitial (i : Fin 4) : ℝ := ![41128,207905,1063932,5501073] i

def refinedLimit (i : Fin 4) : ℝ := ![(20350171/315),(1131587279/3465),(5790778969/3465),(77847356975/9009)] i

def refinedTelescoper (i : Fin 4) (m : ℕ) : ℝ :=
  (refinedNumerator i).eval (m : ℝ)/(refinedDenominator i).eval (m : ℝ)

def refinedCoefficient (i : Fin 4) (m : ℕ) : ℝ :=
  wallisReciprocal m*(∏ l ∈ Finset.range (9+i.val), (2*(m : ℝ)+l+1)^2)*
    (2*m+(9+i.val)+1)/
    ((∏ l ∈ Finset.range (9+i.val), ((m : ℝ)+l+1)^2)*
      (2*m+1)*4^(9+i.val+1)*(m+1)*(m+(9+i.val)+1))

theorem refinedCoefficient_nonneg (i : Fin 4) (m : ℕ) : 0≤refinedCoefficient i m := by
  unfold refinedCoefficient
  have hb := (wallisReciprocal_pos m).le
  positivity

theorem refinedNumerator_degree (i : Fin 4) : (refinedNumerator i).degree=(2*(9+i.val) : ℕ) := by
  fin_cases i <;> norm_num [refinedNumerator] <;> compute_degree!

theorem refinedDenominator_degree (i : Fin 4) : (refinedDenominator i).degree=(2*(9+i.val) : ℕ) := by
  fin_cases i <;> simp only [refinedDenominator, Finset.prod_range_succ,Finset.prod_range_zero] <;>
    compute_degree!

theorem refinedNumerator_leadingCoeff (i : Fin 4) :
    (refinedNumerator i).leadingCoeff=refinedLimit i := by
  rw [Polynomial.leadingCoeff,Polynomial.natDegree_eq_of_degree_eq_some (refinedNumerator_degree i)]
  fin_cases i <;> norm_num [refinedNumerator,refinedLimit] <;> compute_degree!

theorem refinedDenominator_leadingCoeff (i : Fin 4) : (refinedDenominator i).leadingCoeff=1 := by
  unfold refinedDenominator
  exact monic_prod_of_monic _ _ (fun l _ => (monic_X_add_C (l+1 : ℝ)).pow 2)

theorem refinedTelescoper_tendsto (i : Fin 4) :
    Tendsto (refinedTelescoper i) atTop (𝓝 (refinedLimit i)) := by
  have hd : (refinedNumerator i).degree=(refinedDenominator i).degree := by
    rw [refinedNumerator_degree,refinedDenominator_degree]
  have h := (Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
    (refinedNumerator i) (refinedDenominator i) hd).comp tendsto_natCast_atTop_atTop
  change Tendsto (fun m : ℕ => (refinedNumerator i).eval (m : ℝ)/
    (refinedDenominator i).eval (m : ℝ)) atTop (𝓝 (refinedLimit i))
  simpa only [Function.comp_def,refinedNumerator_leadingCoeff,refinedDenominator_leadingCoeff,div_one] using h

theorem refinedTelescoper_initial (i : Fin 4) : refinedTelescoper i 0=refinedInitial i := by
  fin_cases i <;> norm_num [refinedTelescoper,refinedNumerator,refinedDenominator,refinedInitial,
    Finset.prod_range_succ,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow]

private theorem telescoper_step_algebra (W P Q D E x y z b n c a : ℝ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0) (hD : D≠0)
    (hDE : E*x^2=D*y^2) (hPQ : a*Q-y^2*P=n*c*y/(b*x*z)) :
    W*n*c/(D*z*b*x*y)=W*(a/x^2)*(Q/E)-W*(P/D) := by
  have he : E=D*y^2/x^2 := (eq_div_iff (pow_ne_zero 2 hx)).mpr hDE
  calc
    W*n*c/(D*z*b*x*y)=W*(n*c*y/(b*x*z))/(D*y^2) := by
      field_simp [hx,hy,hz,hb,hD]
      <;> ring
    _ = W*(a*Q-y^2*P)/(D*y^2) := by rw [hPQ]
    _ = W*(a/x^2)*(Q/E)-W*(P/D) := by
      rw [he]
      field_simp [hx,hy,hz,hb,hD]
      <;> ring

private theorem refinedDenominator_pos (i : Fin 4) (m : ℕ) :
    0<(refinedDenominator i).eval (m : ℝ) := by
  simp only [refinedDenominator,Polynomial.eval_prod,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
  exact Finset.prod_pos (fun l _ => pow_pos (by positivity) 2)

private theorem refinedDenominator_shift (i : Fin 4) (m : ℕ) :
    (refinedDenominator i).eval ((m : ℝ)+1)*((m : ℝ)+1)^2=
      (refinedDenominator i).eval (m : ℝ)*((m : ℝ)+(9+i.val)+1)^2 := by
  fin_cases i <;>
    norm_num [refinedDenominator,Finset.prod_range_succ,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_pow] <;> ring

set_option maxHeartbeats 10000000 in
/-- Clearing only the two remaining linear factors keeps these exact
polynomial certificates at degree at most twenty-eight. -/
private theorem refinedNumerator_step (i : Fin 4) (m : ℕ) :
    ((2*(m : ℝ)+1)*(2*m+3)/4)*(refinedNumerator i).eval ((m : ℝ)+1)-
      ((m : ℝ)+(9+i.val)+1)^2*(refinedNumerator i).eval (m : ℝ)=
    (∏ l ∈ Finset.range (9+i.val),(2*(m : ℝ)+l+1)^2)*
      (2*m+(9+i.val)+1)*((m : ℝ)+(9+i.val)+1)/
      (4^(9+i.val+1)*((m : ℝ)+1)*(2*m+1)) := by
  fin_cases i <;>
    norm_num [refinedNumerator,Finset.prod_range_succ,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_pow] <;>
    field_simp <;> ring

theorem refinedCoefficient_telescope (i : Fin 4) (m : ℕ) :
    refinedCoefficient i m=wallisReciprocal (m+1)*refinedTelescoper i (m+1)-
      wallisReciprocal m*refinedTelescoper i m := by
  have h := telescoper_step_algebra (wallisReciprocal m)
    ((refinedNumerator i).eval (m : ℝ)) ((refinedNumerator i).eval ((m : ℝ)+1))
    ((refinedDenominator i).eval (m : ℝ)) ((refinedDenominator i).eval ((m : ℝ)+1))
    ((m : ℝ)+1) ((m : ℝ)+(9+i.val)+1) (2*(m : ℝ)+1) (4^(9+i.val+1))
    (∏ l ∈ Finset.range (9+i.val),(2*(m : ℝ)+l+1)^2)
    (2*(m : ℝ)+(9+i.val)+1) ((2*(m : ℝ)+1)*(2*m+3)/4)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (refinedDenominator_pos i m).ne' (refinedDenominator_shift i m) (refinedNumerator_step i m)
  rw [wallisReciprocal_succ]
  simpa only [refinedCoefficient,refinedTelescoper,Nat.cast_add,Nat.cast_one,div_div,
    refinedDenominator,Polynomial.eval_prod,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_C,add_assoc] using h

theorem refinedCoefficient_hasSum (i : Fin 4) :
    HasSum (refinedCoefficient i) (2/Real.pi*refinedLimit i-refinedInitial i) := by
  have h := hasSum_of_wallis_telescope (refinedCoefficient i) (refinedTelescoper i) (refinedLimit i)
    (refinedCoefficient_nonneg i) (refinedCoefficient_telescope i) (refinedTelescoper_tendsto i)
  simpa only [refinedTelescoper_initial] using h

theorem halfPlaneCoefficient_refined_shift (i : Fin 4) (m : ℕ) :
    halfPlaneCoefficient (2*m+(9+i.val)) (9+i.val)=refinedCoefficient i m := by
  unfold halfPlaneCoefficient
  rw [halfPlane_count_real,shifted_choose_ratio]
  unfold refinedCoefficient
  rw [wallisReciprocal_eq_central]
  unfold SpanningTreeIsoperimetry.CornerEnergy.normalizedCentralBinom
  simp only [Finset.prod_pow]
  have hd : (∏ l ∈ Finset.range (9+i.val), ((m : ℝ)+l+1))≠0 :=
    (Finset.prod_pos (fun l _ => by positivity)).ne'
  have hp : (4 : ℝ)^(2*m+(9+i.val)+1)=(4^m)^2*4^(9+i.val+1) := by
    rw [show 2*m+(9+i.val)+1=m*2+(9+i.val+1) by omega,pow_add,pow_mul]
  rw [hp]
  push_cast
  field_simp [hd]
  <;> ring

def refinedValue (i : Fin 4) : ℝ := 2/Real.pi*refinedLimit i-refinedInitial i

theorem halfPlaneCoefficient_refined_hasSum (i : Fin 4) :
    HasSum (fun n => halfPlaneCoefficient n (9+i.val)) (refinedValue i) := by
  have heven : HasSum (fun m => halfPlaneCoefficient (2*m+(9+i.val)) (9+i.val)) (refinedValue i) :=
    (refinedCoefficient_hasSum i).congr_fun (fun m => halfPlaneCoefficient_refined_shift i m)
  have hodd : HasSum (fun m => halfPlaneCoefficient (2*m+1+(9+i.val)) (9+i.val)) (0 : ℝ) := by
    simp [halfPlaneCoefficient,halfPlane_count_wrongParity]
  have hshift : HasSum (fun n => halfPlaneCoefficient (n+(9+i.val)) (9+i.val)) (refinedValue i) := by
    simpa only [add_zero] using heven.even_add_odd
      (f := fun n => halfPlaneCoefficient (n+(9+i.val)) (9+i.val)) hodd
  have hprefix : ∑ n ∈ Finset.range (9+i.val), halfPlaneCoefficient n (9+i.val)=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [halfPlaneCoefficient,halfPlane_count_short (Finset.mem_range.mp hn),Nat.cast_zero,zero_div]
  simpa only [hprefix,zero_add] using hshift.sum_range_add
    (f := fun n => halfPlaneCoefficient n (9+i.val)) (k := 9+i.val)

def boundaryValueThirteen (j : Fin 13) : ℝ :=
  if h : j.val<9 then boundaryValueNine ⟨j.val,h⟩ else refinedValue ⟨j.val-9,by omega⟩

theorem halfPlaneCoefficient_thirteen_hasSum (j : Fin 13) :
    HasSum (fun n => halfPlaneCoefficient n j.val) (boundaryValueThirteen j) := by
  unfold boundaryValueThirteen
  split_ifs with h
  · exact halfPlaneCoefficient_nine_hasSum ⟨j.val,h⟩
  · have hi : 9+(j.val-9)=j.val := by omega
    simpa only [hi] using halfPlaneCoefficient_refined_hasSum ⟨j.val-9,by omega⟩

def planeEntry13 (t : ℝ) (j : Fin 13) : ℝ :=
  if h : j.val<9 then BoundaryGreenPolynomials.planeEntry t ⟨j.val,h⟩
  else 2*t*refinedLimit ⟨j.val-9,by omega⟩-refinedInitial ⟨j.val-9,by omega⟩

theorem boundaryValueThirteen_eq (j : Fin 13) :
    boundaryValueThirteen j=planeEntry13 (1/Real.pi) j := by
  unfold boundaryValueThirteen planeEntry13
  split_ifs with h
  · exact BoundaryGreenPolynomials.boundaryValueNine_eq ⟨j.val,h⟩
  · unfold refinedValue
    ring

end
end SpanningTreeIsoperimetry.BoundaryGreenRefined
