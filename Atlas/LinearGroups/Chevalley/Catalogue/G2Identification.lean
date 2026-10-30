import Atlas.LinearGroups.Chevalley.Catalogue.G2Construction
import Atlas.LinearGroups.Chevalley.Comparison.G2.OctonionEquiv

/-! Source-only registration of the existing, audited actual marked equivalence. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

/-- The typed parameter map is literally the same field with the same operations. -/
abbrev G2_octonionField (K : Type*) : Type _ := K

/-- A named value of the existing target operations, not another registered instance. -/
def G2OctonionGroup (K : Type*) [Field K] : Group (Atlas.G2.Model K) := inferInstance

/-- The already audited map; its domain includes the full binary group. -/
def G2_identification (K : Type*) [Field K] (hK : G2FieldDomain K) :
    G2 K ≃* Atlas.G2.Model (G2_octonionField K) := by
  letI : Finite K := hK
  exact Comparison.G2.octonionEquiv K

theorem G2_identification_X (K : Type*) [Field K] (hK : G2FieldDomain K)
    (i : Fin 2) (t : K) :
    G2_identification K hK (modelX .G2 K i t) =
      Comparison.G2.octonionSimpleRoot K (Fin.castAdd 2 i) t := by
  letI : Finite K := hK
  exact Comparison.G2.octonionEquiv_X K i t

theorem G2_identification_Y (K : Type*) [Field K] (hK : G2FieldDomain K)
    (i : Fin 2) (t : K) :
    G2_identification K hK (modelY .G2 K i t) =
      Comparison.G2.octonionSimpleRoot K (Fin.natAdd 2 i) t := by
  letI : Finite K := hK
  exact Comparison.G2.octonionEquiv_Y K i t

end Atlas.Chevalley.Catalogue
