module

public import SpanningTreeIsoperimetry.AspectCost

@[expose] public section

/-! Light definitions for the small-family cost and derivative certificates. -/
namespace SpanningTreeIsoperimetry.SmallFamilyMonotonicity
open AspectCost
open scoped BigOperators
noncomputable section
def aspectStep (a h r : ℝ) : ℝ := D ((a+2*h)/(r-h))-D (a/r)

def normalizedSlope (a h r : ℝ) : ℝ :=
  (h/4)*(r^3/(r-h)^2*(2*r*(a+h)-a*h))+
  (h*(Real.pi-3)/12)*(2*r^3+(4*h+2*a)*(r^3/(r-h))+(2*h^2+a*h)*(r^3/(r-h)^2))

variable {ι : Type*}
def weightedLoss (I : Finset ι) (c shift : ι → ℝ) (r : ℝ) : ℝ := ∑ i∈I,c i/(r-shift i)^4
def normalizedWeight (I : Finset ι) (c shift : ι → ℝ) (r : ℝ) : ℝ := 4*∑ i∈I,c i*(r/(r-shift i))^5

end
end SpanningTreeIsoperimetry.SmallFamilyMonotonicity

namespace SpanningTreeIsoperimetry.SmallFamilyCosts
open SmallFamilyMonotonicity
open scoped BigOperators
noncomputable section
def remainderBound (q a b g r : ℝ) : ℝ :=
  g/(2*(r-a)^2*(r-b)^2)+1/(4*(r-b)^4)+q/(r-a)^4

variable {ι : Type*}
def upperCost (C q sourceShift a h : ℝ) (I : Finset ι) (c shift : ι → ℝ) (r : ℝ) : ℝ :=
  C+aspectStep a h r+remainderBound q h sourceShift (h*(a+h)) r-weightedLoss I c shift r

end
end SpanningTreeIsoperimetry.SmallFamilyCosts
