module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-! Exact profile data for the small noncanonical family comparisons. These
are definitions only; derivative and endpoint certificates are separate. -/
namespace SpanningTreeIsoperimetry.SmallFamilyProfiles
noncomputable section

def gap : Fin 26 → ℝ := ![0,1,0,1,1,2,0,0,1,1,2,0,0,0,1,1,2,0,0,0,0,2,0,2,3,2]
def hullShift : Fin 26 → ℝ := ![1,1,1,1,1,1,2,2,1,1,1,2,2,2,1,1,1,2,2,2,2,1,2,1,1,1]
def leftEnd : Fin 26 → ℝ := ![5,4,5,5,5,4,6,6,5,5,5,6,6,6,6,6,6,7,7,7,8,7,9,6,8,4]
def coeff : Fin 26 → Fin 4 → ℝ :=
  ![![24/5,0,0,0], ![10/3,0,0,0], ![0,0,0,0], ![83/12,0,0,0],
    ![5,0,0,0], ![5,0,0,0], ![24/5,5/3,5/3,0], ![48/5,0,0,0],
    ![21/2,0,0,0], ![20/3,0,0,0], ![559/60,0,0,0], ![153/20,0,5/3,3/4],
    ![112/5,0,0,0], ![12,0,0,0], ![73/6,0,0,0], ![25/3,0,0,0],
    ![0,0,0,0], ![36/5,5/3,5/3,5/3], ![72/5,0,0,0], ![0,0,0,0],
    ![84/5,0,0,0], ![10,0,0,0], ![35/3,0,0,0], ![20,0,0,0],
    ![70/3,0,0,0], ![10/3,5/3,0,0]]

def shifts (i : Fin 4) : ℝ := i.val

/-- Keep the side-three remainder coefficient throughout these families. -/
def errorCoeff (j : Fin 26) : ℝ := if j=1 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=25 then 1/3 else 1/4

/-- The common evenT2,j4 bound uses source side m−1 and target side m−2. -/
def sourceShift (j : Fin 26) : ℝ := if j=22 then 1 else 0

/-- 0: zero;1:E1(4,6);2:E2(4,6);3:E2(4,7);4:E2(5,7);
5:E3(5,8);6:E3(6,10);7:E4(7,11);8:E2+B(7,12,2). -/
def targetCapKind : Fin 26 → Fin 9 :=
  ![1,0,2,1,1,0,0,0,3,3,1,1,1,1,5,5,4,4,4,4,6,6,7,1,8,0]

end
end SpanningTreeIsoperimetry.SmallFamilyProfiles
