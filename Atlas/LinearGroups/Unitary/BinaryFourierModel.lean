import Atlas.LinearGroups.Unitary.BinaryFourBridge
import Atlas.LinearGroups.Unitary.CoordinateStabilizer

/-! Actual binary SU₃ Fourier element, restricted from the checked rank-four bridge. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable [CharP K 2]

def binaryBridgeStabilizer (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2)
    (c : K) (hc : c^2+c+1=0) : firstSpecialStabilizer (n := 3) hdeg :=
  ⟨binaryBridgeElement hdeg hq c hc, by
    apply Subtype.ext
    change (binaryBridgeElement hdeg hq c hc).val *ᵥ Pi.single 0 1 = Pi.single 0 1
    rw [binaryBridgeElement_matrix]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [extendMatrix, mulVec, dotProduct, Fin.sum_univ_succ, Pi.single_apply]
⟩

def binaryFourierUnitary (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2)
    (c : K) (hc : c^2+c+1=0) : SU F K 3 hdeg :=
  restrictSpecial hdeg (binaryBridgeStabilizer hdeg hq c hc)

theorem binaryFourierUnitary_matrix (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2)
    (c : K) (hc : c^2+c+1=0) : (binaryFourierUnitary hdeg hq c hc).val = binaryFourierThree c := by
  change restrictMatrix (binaryBridgeElement hdeg hq c hc).val = _
  rw [binaryBridgeElement_matrix]
  rfl

theorem binaryFourier_not_coordinateStabilizer (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2) (c : K) (hc : c^2+c+1=0) :
    binaryFourierUnitary hdeg hq c hc ∉ coordinateStabilizer hdeg 3 := by
  intro h
  obtain ⟨i,a,ha⟩ := coordinateStabilizer_columns hdeg _ h 0
  rw [binaryFourierUnitary_matrix] at ha
  fin_cases i
  · have he := congrFun ha 1
    simpa [binaryFourierThree, mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply] using he
  · have he := congrFun ha 0
    simpa [binaryFourierThree, mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply] using he
  · have he := congrFun ha 0
    simpa [binaryFourierThree, mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply] using he
end Atlas.Unitary
