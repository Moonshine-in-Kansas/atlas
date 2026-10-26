import Atlas.LinearGroups.Orthogonal.Minus.AllRanks

/-! Public half-dimension wrappers for the completed norm-plane comparisons. -/
noncomputable section
namespace Atlas.Comparisons.Classical
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def dMinusTwoEquivA1 (hdeg : Module.finrank F K = 2) :
    Atlas.Orthogonal.DMinus 2 F K hdeg ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  Atlas.Orthogonal.Minus.family_rankTwo_equiv hdeg

def dMinusThreeEquivUnitary (hdeg : Module.finrank F K = 2) :
    Atlas.Orthogonal.DMinus 3 F K hdeg ≃* Atlas.Unitary.PSU F K 4 hdeg :=
  Atlas.Orthogonal.Minus.family_rankThree_equiv hdeg

@[simp] theorem dMinusThreeEquivUnitary_inverse (hdeg : Module.finrank F K = 2)
    (g : Atlas.Unitary.PSU F K 4 hdeg) :
    dMinusThreeEquivUnitary hdeg ((dMinusThreeEquivUnitary hdeg).symm g) = g :=
  (dMinusThreeEquivUnitary hdeg).apply_symm_apply g
end Atlas.Comparisons.Classical
