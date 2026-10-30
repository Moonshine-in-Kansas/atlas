import Atlas.LinearGroups.Chevalley.Catalogue.F4Construction
import Atlas.LinearGroups.Chevalley.Comparison.F4.AlbertEquiv

/-! Typed catalogue interface to the marked Chevalley–Albert equivalence.
The field is unchanged; the existing negative Albert parameter is -t. -/
noncomputable section
namespace Atlas.Chevalley.Catalogue

abbrev F4_albertField (K : Type*) : Type _ := K

def F4AlbertGroup (K : Type*) [Field K] : Group (Atlas.F4.Model K) := inferInstance

def F4_identification (K : Type*) [Field K] (hK : F4FieldDomain K) :
    F4 K ≃* Atlas.F4.Model (F4_albertField K) := by
  letI : Finite K := hK
  exact Comparison.F4.albertEquiv K

theorem F4_identification_X (K : Type*) [Field K] (hK : F4FieldDomain K)
    (i : Fin 4) (t : K) :
    F4_identification K hK (modelX .F4 K i t) = Atlas.F4.simplePositive i t := by
  letI : Finite K := hK
  exact Comparison.F4.albertEquiv_simplePositive K i t

theorem F4_identification_Y (K : Type*) [Field K] (hK : F4FieldDomain K)
    (i : Fin 4) (t : K) :
    F4_identification K hK (modelY .F4 K i t) = Atlas.F4.simpleNegative i (-t) := by
  letI : Finite K := hK
  exact Comparison.F4.albertEquiv_simpleNegative K i t

end Atlas.Chevalley.Catalogue
