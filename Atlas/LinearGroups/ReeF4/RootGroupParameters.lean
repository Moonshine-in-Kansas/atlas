import Atlas.LinearGroups.ReeF4.RootGroupEquiv

/-! Recovery of the two root parameters from actual matrix entries. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

theorem shortRootPairLinear_first_entry (τ : F →+* F) (a b : F) :
    (shortRootPairLinear τ a b (rootVector (1,0))).val.2 2 0 = a := by
  change (shortRootParameterLinear τ a (shortRootCenterLinear τ b (rootVector (1,0)))).val.2 2 0 = a
  rw [shortRootParameterLinear_val, shortRootCenterLinear_val]
  simp [shortRootParameterFormula, shortRootCenterFormula, rootVector,
    Pi.single_apply, Fin.ext_iff]

theorem shortRootPairLinear_second_entry (τ : F →+* F) (a b : F) :
    (shortRootPairLinear τ a b (rootVector (1,1))).val.2 2 0 = a*τ a+b := by
  change (shortRootParameterLinear τ a (shortRootCenterLinear τ b (rootVector (1,1)))).val.2 2 0 = _
  rw [shortRootParameterLinear_val, shortRootCenterLinear_val]
  simp [shortRootParameterFormula, shortRootCenterFormula, rootVector,
    Pi.single_apply, Fin.ext_iff]
  ring

theorem shortRootPairLinear_injective (τ : F →+* F) :
    Function.Injective (fun p : F × F => shortRootPairLinear τ p.1 p.2) := by
  intro p q h
  have ha := congrArg (fun g : Module.End F (TraceZero F) => (g (rootVector (1,0))).val.2 2 0) h
  simp only [shortRootPairLinear_first_entry] at ha
  have hb := congrArg (fun g : Module.End F (TraceZero F) => (g (rootVector (1,1))).val.2 2 0) h
  simp only [shortRootPairLinear_second_entry] at hb
  rw [ha] at hb
  exact Prod.ext ha (add_left_cancel hb)

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem shortRootPairEquiv_injective (m : ℕ) (hcard : Nat.card K = 2^(2*m+1)) :
    Function.Injective (fun p : K × K => shortRootPairEquiv m hcard p.1 p.2) := by
  intro p q h
  apply shortRootPairLinear_injective (theta K m).toRingHom
  exact congrArg LinearEquiv.toLinearMap h

end Atlas.ReeF4
