import Atlas.LinearGroups.Triality.FieldTransport
import Mathlib.FieldTheory.Finite.GaloisField

/-! A base-field equivalence extends to compatible cubic finite fields. -/
noncomputable section
namespace Atlas.Triality
open Polynomial
variable {F E K L : Type*} [Field F] [Field E] [Field K] [Field L]
  [Finite F] [Finite E] [Finite K] [Finite L] [Algebra F K] [Algebra E L]

theorem compatibleCubicEquiv_exists (eF : F ≃+* E)
    (hK : Module.finrank F K=3) (hL : Module.finrank E L=3) :
    ∃ eK : K ≃+* L, ∀ t, eK (algebraMap F K t)=algebraMap E L (eF t) := by
  letI : Algebra F L := ((algebraMap E L).comp eF.toRingHom).toAlgebra
  letI := Fintype.ofFinite K
  letI := Fintype.ofFinite L
  have hcard : Nat.card K=Nat.card L := by
    rw [FiniteCubic.card_extension hK,FiniteCubic.card_extension hL,Nat.card_congr eF.toEquiv]
  let P : F[X] := X^Nat.card K-X
  letI : IsSplittingField F K P := by
    dsimp [P]
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.isSplittingField_sub K F
  letI : IsSplittingField F L P := by
    dsimp [P]
    rw [hcard,Nat.card_eq_fintype_card]
    exact FiniteField.isSplittingField_sub L F
  let e : K ≃ₐ[F] L := (IsSplittingField.algEquiv K P).trans
    (IsSplittingField.algEquiv L P).symm
  exact ⟨e.toRingEquiv,fun t => e.commutes t⟩

def cubicFieldEquiv (eF : F ≃+* E)
    (hK : Module.finrank F K=3) (hL : Module.finrank E L=3) : K ≃+* L :=
  Classical.choose (compatibleCubicEquiv_exists eF hK hL)

theorem cubicFieldEquiv_compatible (eF : F ≃+* E)
    (hK : Module.finrank F K=3) (hL : Module.finrank E L=3) (t : F) :
    cubicFieldEquiv eF hK hL (algebraMap F K t)=algebraMap E L (eF t) :=
  Classical.choose_spec (compatibleCubicEquiv_exists eF hK hL) t

def baseFieldEquiv (eF : F ≃+* E)
    (hK : Module.finrank F K=3) (hL : Module.finrank E L=3) : Group F K ≃* Group E L :=
  fieldEquiv eF (cubicFieldEquiv eF hK hL) (cubicFieldEquiv_compatible eF hK hL)

end Atlas.Triality
