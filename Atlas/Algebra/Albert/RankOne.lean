import Atlas.Algebra.Albert.TracePairing

namespace Atlas.Albert
variable {F : Type*} [CommRing F]

def IsRankOne (x : Carrier F) : Prop := x ≠ 0 ∧ adjoint x = 0
def WhiteZeroVectors (F : Type*) [CommRing F] :=
  {x : Carrier F // IsRankOne x ∧ trace x = 0}
def TraceOneRankOne (F : Type*) [CommRing F] :=
  {x : Carrier F // adjoint x = 0 ∧ trace x = 1}

/-- The marked off-diagonal singular vector, using split-octonion index zero. -/
def baseVector : Carrier F := (0, ![SplitOctonion.basisVector 0, 0, 0])

theorem baseVector_trace : trace (baseVector : Carrier F) = 0 := by
  simp [trace, baseVector]

theorem baseVector_adjoint : adjoint (baseVector : Carrier F) = 0 := by
  apply Prod.ext
  · funext i; fin_cases i <;>
      simp [baseVector, adjoint, SplitOctonion.basisVector, SplitOctonion.norm]
  · funext i j; fin_cases i <;> fin_cases j <;>
      simp [baseVector, adjoint, SplitOctonion.basisVector, SplitOctonion.conjugate,
        SplitOctonion.mul, SplitOctonion.trace, SplitOctonion.unit]

theorem baseVector_ne_zero [Nontrivial F] : (baseVector : Carrier F) ≠ 0 := by
  intro h
  have := congrArg (fun x : Carrier F => x.2 0 0) h
  simpa [baseVector, SplitOctonion.basisVector] using this

def markedWhiteZeroVector [Nontrivial F] : WhiteZeroVectors F :=
  ⟨baseVector, ⟨baseVector_ne_zero, baseVector_adjoint⟩, baseVector_trace⟩

theorem adjoint_eq_zero_iff_pairing (x : Carrier F) :
    adjoint x = 0 ↔ ∀ y, tracePairing (adjoint x) y = 0 := by
  constructor
  · intro h y
    rw [h]
    simp [tracePairing, trace, quadraticTrace, SplitOctonion.norm]
  · exact tracePairing_nondegenerate _

end Atlas.Albert
