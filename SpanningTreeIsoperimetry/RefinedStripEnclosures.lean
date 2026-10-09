import SpanningTreeIsoperimetry.RefinedStripPolynomials
import SpanningTreeIsoperimetry.RefinedPiBounds

/-! Rational enclosures around a common reciprocal-pi center. All centered
polynomial identities and all interval inequalities are kernel checked. -/
namespace SpanningTreeIsoperimetry.RefinedStripEnclosures
open RefinedStripPolynomials RefinedPiBounds
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def centered1 (u : ℝ) : ℝ := (2834505690810466423/9375000000000000000) + (-16/3)*u^1

set_option maxHeartbeats 4000000 in
theorem stripDet1_centered (t : ℝ) : stripDet1 t=centered1 (t-center) := by
  unfold stripDet1 centered1 center
  ring

set_option maxHeartbeats 4000000 in
theorem stripDet1_bounds : (3023472736 : ℝ)/10000000000<stripDet1 (1/Real.pi) ∧
    stripDet1 (1/Real.pi)<(3023472737 : ℝ)/10000000000 := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  norm_num [radius] at hl1 hu1
  rw [stripDet1_centered]
  unfold centered1
  simp only [one_div]
  constructor <;> nlinarith only [hl1,hu1]

def centered2 (u : ℝ) : ℝ := (1279508615755904136298624562810414929/13732910156250000000000000000000000000) + (-2248568190810466423/137329101562500000)*u^1 + (8192/45)*u^2

set_option maxHeartbeats 4000000 in
theorem stripDet2_centered (t : ℝ) : stripDet2 t=centered2 (t-center) := by
  unfold stripDet2 centered2 center
  ring

set_option maxHeartbeats 4000000 in
theorem stripDet2_bounds : (931709740 : ℝ)/10000000000<stripDet2 (1/Real.pi) ∧
    stripDet2 (1/Real.pi)<(931709741 : ℝ)/10000000000 := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  norm_num [radius] at hl1 hu1 hl2 hu2
  rw [stripDet2_centered]
  unfold centered2
  simp only [one_div]
  constructor <;> nlinarith only [hl1,hu1,hl2,hu2]

def centered3 (u : ℝ) : ℝ := (211705879637069963059462751342154031657126980902428967/7334165275096893310546875000000000000000000000000000000) + (-13700553410514956274203490875931244787/146683305501937866210937500000000000)*u^1 + (2042525370542438212864/751018524169921875)*u^2 + (-134217728/7875)*u^3

set_option maxHeartbeats 4000000 in
theorem stripDet3_centered (t : ℝ) : stripDet3 t=centered3 (t-center) := by
  unfold stripDet3 centered3 center
  ring

set_option maxHeartbeats 4000000 in
theorem stripDet3_bounds : (288657088 : ℝ)/10000000000<stripDet3 (1/Real.pi) ∧
    stripDet3 (1/Real.pi)<(288657089 : ℝ)/10000000000 := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  obtain ⟨hl3,hu3⟩ := abs_le.mp (power_bounds 3)
  norm_num [radius] at hl1 hu1 hl2 hu2 hl3 hu3
  rw [stripDet3_centered]
  unfold centered3
  simp only [one_div]
  constructor <;> nlinarith only [hl1,hu1,hl2,hu2,hl3,hu3]

def centered4 (u : ℝ) : ℝ := (6911264626753058100628051474920554635458172277057208430503781661700041/771133157329018104064743965864181518554687500000000000000000000000000000) + (-1293173742013177169386007224120084802496148863376019171/1927832893322545260161859914660453796386718750000000)*u^1 + (4035571838585526196481510302317864887296/52642690206994302570819854736328125)*u^2 + (-2730900110589210255322775552/1655995845794677734375)*u^3 + (140737488355328/17364375)*u^4

set_option maxHeartbeats 4000000 in
theorem stripDet4_centered (t : ℝ) : stripDet4 t=centered4 (t-center) := by
  unfold stripDet4 centered4 center
  ring

set_option maxHeartbeats 4000000 in
theorem stripDet4_bounds : (89624788 : ℝ)/10000000000<stripDet4 (1/Real.pi) ∧
    stripDet4 (1/Real.pi)<(89624789 : ℝ)/10000000000 := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  obtain ⟨hl3,hu3⟩ := abs_le.mp (power_bounds 3)
  obtain ⟨hl4,hu4⟩ := abs_le.mp (power_bounds 4)
  norm_num [radius] at hl1 hu1 hl2 hu2 hl3 hu3 hl4 hu4
  rw [stripDet4_centered]
  unfold centered4
  simp only [one_div]
  constructor <;> nlinarith only [hl1,hu1,hl2,hu2,hl3,hu3,hl4,hu4]

def centered5 (u : ℝ) : ℝ := (17888888456281147182729911919257521965786938827546490205784914349924145790869392171660183/6421452048459549218246966706402645286289043724536895751953125000000000000000000000000000000) + (-134774787462197143544850051754716793453892633199195525108599192562182319871/25685808193838196872987866825610581145156174898147583007812500000000000)*u^1 + (860975155573140797134465356428624778101354339242405669562624/131511337952451567989697878147126175463199615478515625)*u^2 + (-377532984994917214037139007152848479491922591744/1378996327048298553563654422760009765625)*u^3 + (50109302082819707722965355155423232/14459824526309967041015625)*u^4 + (-9444732965739290427392/758111248125)*u^5

set_option maxHeartbeats 4000000 in
theorem stripDet5_centered (t : ℝ) : stripDet5 t=centered5 (t-center) := by
  unfold stripDet5 centered5 center
  ring

set_option maxHeartbeats 4000000 in
theorem stripDet5_bounds : (27858011 : ℝ)/10000000000<stripDet5 (1/Real.pi) ∧
    stripDet5 (1/Real.pi)<(27858012 : ℝ)/10000000000 := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  obtain ⟨hl3,hu3⟩ := abs_le.mp (power_bounds 3)
  obtain ⟨hl4,hu4⟩ := abs_le.mp (power_bounds 4)
  obtain ⟨hl5,hu5⟩ := abs_le.mp (power_bounds 5)
  norm_num [radius] at hl1 hu1 hl2 hu2 hl3 hu3 hl4 hu4 hl5 hu5
  rw [stripDet5_centered]
  unfold centered5
  simp only [one_div]
  constructor <;> nlinarith only [hl1,hu1,hl2,hu2,hl3,hu3,hl4,hu4,hl5,hu5]

def centered6 (u : ℝ) : ℝ := (78875164353717570132349398346283370716404632805000316722228827879395760066713367118770767189073213365095757/91031953318160944172724173589391099723714534386331820314808283001184463500976562500000000000000000000000000000) + (-1638511345741586108596758029226172176290772080289410168535236190622644826999759870456736022473/37929980549233726738635072328912958218214389327638258464503451250493526458740234375000000)*u^1 + (377073108672997778388884811709857752365359878461849163946583128674038046080351232/414296534212430252590531350024606604964816369829350151121616363525390625)*u^2 + (-3714291142181943563568162353545169960770251119351581767136452703944704/39097926239249993808633210079506170586682856082916259765625)*u^3 + (384017318296926881565585750276468210925283556926009901056/136657157014159338359604589641094207763671875)*u^4 + (-1810341495428707878428046055842459645116416/61237356868922710418701171875)*u^5 + (20282409603651670423947251286016/225384199733818125)*u^6

set_option maxHeartbeats 4000000 in
theorem stripDet6_centered (t : ℝ) : stripDet6 t=centered6 (t-center) := by
  unfold stripDet6 centered6 center
  ring

set_option maxHeartbeats 4000000 in
theorem stripDet6_bounds : (8664558 : ℝ)/10000000000<stripDet6 (1/Real.pi) ∧
    stripDet6 (1/Real.pi)<(8664559 : ℝ)/10000000000 := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  obtain ⟨hl3,hu3⟩ := abs_le.mp (power_bounds 3)
  obtain ⟨hl4,hu4⟩ := abs_le.mp (power_bounds 4)
  obtain ⟨hl5,hu5⟩ := abs_le.mp (power_bounds 5)
  obtain ⟨hl6,hu6⟩ := abs_le.mp (power_bounds 6)
  norm_num [radius] at hl1 hu1 hl2 hu2 hl3 hu3 hl4 hu4 hl5 hu5 hl6 hu6
  rw [stripDet6_centered]
  unfold centered6
  simp only [one_div]
  constructor <;> nlinarith only [hl1,hu1,hl2,hu2,hl3,hu3,hl4,hu4,hl5,hu5,hl6,hu6]

end
end SpanningTreeIsoperimetry.RefinedStripEnclosures
