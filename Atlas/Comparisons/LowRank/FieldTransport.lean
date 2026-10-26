import Atlas.Comparisons.LowRank.Unitary
import Atlas.Comparisons.LowRank.MinusOrthogonal
import Atlas.LinearGroups.Unitary.BaseFieldTransport

/-! Transport retains the actual quadratic and Hermitian carriers. The minus map
requires the commutative base/extension square; the unitary map uses Frobenius
involutions and their already proved compatibility with entrywise transport. -/
noncomputable section
namespace Atlas.Comparisons.Classical
variable {F K F' K' : Type*} [Field F] [Field K] [Field F'] [Field K']
  [Finite F] [Finite K] [Finite F'] [Finite K'] [Algebra F K] [Algebra F' K']

def unitaryFieldEquiv (e : F ≃+* F') (f : K ≃+* K')
    (hdeg : Module.finrank F K = 2) (hdeg' : Module.finrank F' K' = 2) (d : ℕ) :
    Atlas.Unitary.PSU F K d hdeg ≃* Atlas.Unitary.PSU F' K' d hdeg' :=
  Atlas.Unitary.projectiveUnitaryBaseChangeEquiv f (Nat.card_congr e.toEquiv) hdeg hdeg' d

def dMinusFieldEquiv (e : F ≃+* F') (f : K ≃+* K')
    (hc : ∀ a : F, f (algebraMap F K a) = algebraMap F' K' (e a))
    (hdeg : Module.finrank F K = 2) (hdeg' : Module.finrank F' K' = 2) (n : ℕ) :
    Atlas.Orthogonal.DMinus n F K hdeg ≃* Atlas.Orthogonal.DMinus n F' K' hdeg' :=
  Atlas.Orthogonal.Minus.fieldEquivProjective e f hc hdeg hdeg' (n-1)
end Atlas.Comparisons.Classical
