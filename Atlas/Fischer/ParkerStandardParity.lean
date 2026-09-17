import Atlas.Fischer.ParkerStandardAutomorphisms

namespace Atlas.Fischer
open Atlas.Codes

theorem parkerStandard_preserves_sign (e : ParkerStandardGroup) (s : Bit) (x : ParkerLoop) :
    e.val (parkerSign s x) = parkerSign s (e.val x) := by
  have hx : parkerSign s x = parkerLoopMultiply x (0, s) := by
    simp [parkerSign, parkerLoopMultiply, parkerMultiply]
  rw [hx, e.property.1, e.property.2.1]
  simp [parkerSign, parkerLoopMultiply, parkerMultiply]

theorem parkerCodeEquiv_golayOne (g : Mathieu24CodeModel) :
    parkerCodeEquiv g golayOne = golayOne := by
  apply Subtype.ext
  rfl

theorem parkerStandard_omega_first (e : ParkerStandardGroup) :
    (e.val parkerOmega).1 = golayOne := by
  rw [parkerStandardProjection_spec]
  exact parkerCodeEquiv_golayOne _

theorem parkerStandard_omega (e : ParkerStandardGroup) :
    e.val parkerOmega = parkerSign (e.val parkerOmega).2 parkerOmega := by
  apply Prod.ext
  · exact parkerStandard_omega_first e
  · change (e.val parkerOmega).2 = 0 + (e.val parkerOmega).2
    simp

noncomputable def parkerStandardParity : ParkerStandardGroup →* Multiplicative Bit where
  toFun e := Multiplicative.ofAdd (e.val parkerOmega).2
  map_one' := rfl
  map_mul' e f := by
    change Multiplicative.ofAdd (e.val (f.val parkerOmega)).2 =
      Multiplicative.ofAdd ((e.val parkerOmega).2 + (f.val parkerOmega).2)
    rw [parkerStandard_omega f, parkerStandard_preserves_sign]
    simp [parkerSign, parkerOmega]

noncomputable def parkerStandardPlus : Subgroup ParkerStandardGroup := parkerStandardParity.ker

theorem parkerStandardPlus_iff (e : ParkerStandardGroup) :
    e ∈ parkerStandardPlus ↔ e.val parkerOmega = parkerOmega := by
  change (e.val parkerOmega).2 = 0 ↔ _
  constructor
  · intro h
    rw [parkerStandard_omega e, h, parkerSign_zero]
  · intro h
    exact congrArg Prod.snd h

theorem cocodeParity_coordinate (p : Omega) :
    cocodeParity (Submodule.Quotient.mk (Pi.single p (1 : Bit) : BinaryWord)) = 1 := by
  rw [cocodeParity_mk]
  simp [binaryDot_apply, allOnes, Pi.single_apply]

theorem cocodeParity_surjective : Function.Surjective cocodeParity := by
  intro s
  have hs : ∀ r : Bit, r = 0 ∨ r = 1 := by decide
  rcases hs s with rfl | rfl
  · exact ⟨0, map_zero _⟩
  · exact ⟨Submodule.Quotient.mk (Pi.single (Classical.arbitrary Omega) (1 : Bit) : BinaryWord),
      cocodeParity_coordinate _⟩

end Atlas.Fischer
