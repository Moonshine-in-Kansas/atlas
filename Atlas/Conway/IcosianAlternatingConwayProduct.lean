import Atlas.Conway.IcosianScalarConwayProduct
import Atlas.Algebra.GoldenFourAlternating

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra

/-- The scalar sign quotient is the actual A5, via its five-point projective action. -/
def icosianScalarProjectiveAlternating :
    IcosianScalarProjectiveModel ≃* alternatingGroup (Fin 5) :=
  icosianScalarProjectiveSL.trans goldenFourSLAlternatingFive

/-- The concrete A5 times quaternionic projective group inside the retained Co1. -/
def icosianAlternatingProjectiveToCo1 :
    alternatingGroup (Fin 5) × IcosianProjectiveModel →* LeechCentralQuotient :=
  icosianScalarProjectiveProductToCo1.comp
    (icosianScalarProjectiveAlternating.symm.prodCongr (MulEquiv.refl _)).toMonoidHom

theorem icosianAlternatingProjectiveToCo1_injective :
    Function.Injective icosianAlternatingProjectiveToCo1 :=
  icosianScalarProjectiveProductToCo1_injective.comp
    (icosianScalarProjectiveAlternating.symm.prodCongr (MulEquiv.refl _)).injective

end Atlas.Conway
