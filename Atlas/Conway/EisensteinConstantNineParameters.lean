import Atlas.Conway.EisensteinNineHexadFamily
import Atlas.Codes.TernaryHexadAffinePhases

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

/-- Select either member of a complementary constant-hexad partition. -/
def eisensteinNinePartitionSide (p : TernaryConstantHexadPair) (r : Bool) : Finset (Fin 12) :=
  if r then (eisensteinHexadPairSupport p)ᶜ else eisensteinHexadPairSupport p

theorem eisensteinNinePartitionSide_mem (p : TernaryConstantHexadPair) (r : Bool) :
    eisensteinNinePartitionSide p r ∈ ternaryConstantHexads := by
  cases r
  · exact eisensteinHexadPairSupport_mem p
  · exact ternaryConstantHexads_compl _ (eisensteinHexadPairSupport_mem p)

def eisensteinNinePartitionCode (p : TernaryConstantHexadPair) (r : Bool) : TernarySixWords :=
  ternaryConstantHexadCodeword _ (eisensteinNinePartitionSide_mem p r)

/-- The parameters of all oriented constant norm-nine vectors for a fixed partition/sign:
side, overall sign, outside heavy point, affine support phases, and heavy phase. -/
abbrev EisensteinConstantNineParameters (p : TernaryConstantHexadPair) (b : ZMod 3) :=
  (r : Bool) × Bool × {j : Fin 12 // j ∉ ternarySupport (eisensteinNinePartitionCode p r).val.val} ×
    TernaryHexadAffinePhase (eisensteinNinePartitionCode p r) b × ZMod 3

theorem eisensteinConstantNineParameters_card (p : TernaryConstantHexadPair) (b : ZMod 3) :
    Nat.card (EisensteinConstantNineParameters p b)=17496 := by
  classical
  rw [Nat.card_sigma]
  have ho (r : Bool) :
      Nat.card {j : Fin 12 // j ∉ ternarySupport (eisensteinNinePartitionCode p r).val.val}=6 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe,
      ternarySupport_card,(eisensteinNinePartitionCode p r).property]
  have hr (r : Bool) : Nat.card (Bool ×
      {j : Fin 12 // j ∉ ternarySupport (eisensteinNinePartitionCode p r).val.val} ×
      TernaryHexadAffinePhase (eisensteinNinePartitionCode p r) b × ZMod 3)=8748 := by
    rw [Nat.card_prod,Nat.card_prod,Nat.card_prod,ho,ternaryHexadAffinePhase_card]
    norm_num
  simp_rw [hr]
  norm_num

def eisensteinConstantNinePhaseWord (p : TernaryConstantHexadPair) (r : Bool) (b : ZMod 3)
    (a : TernaryHexadAffinePhase (eisensteinNinePartitionCode p r) b) : TernaryWord :=
  fun i => if h : i ∈ ternarySupport (eisensteinNinePartitionCode p r).val.val then a.val ⟨i,h⟩ else 0

def eisensteinConstantNineParameterLift (p : TernaryConstantHexadPair) (b : ZMod 3)
    (a : EisensteinConstantNineParameters p b) : EisensteinCoordinates := fun i =>
  (if a.2.1 then (-1 : Eisenstein) else 1)*
    ((if i ∈ eisensteinNinePartitionSide p a.1 then
      eisensteinPhase (eisensteinConstantNinePhaseWord p a.1 b a.2.2.2.1 i) else 0)-
      if i=a.2.2.1.val then
        eisensteinTheta*eisensteinPhaseCorrection b*eisensteinPhase a.2.2.2.2 else 0)

def eisensteinConstantNineParameterVector (p : TernaryConstantHexadPair) (b : ZMod 3)
    (a : EisensteinConstantNineParameters p b) : EisensteinCoordinates :=
  eisensteinTheta • eisensteinConstantNineParameterLift p b a

end Atlas.Conway
