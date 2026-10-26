import Atlas.LinearGroups.Chevalley.Integral.RankTwo.B2ExponentialTransport
import Mathlib.Algebra.Group.Units.Equiv

/-! UNCHECKED generated-group restriction of the actual coordinate permutation.
This is a comparison between the two new Chevalley models only. It does not
identify either with an earlier orthogonal or symplectic ATLAS construction. -/
noncomputable section
namespace Atlas.Chevalley.Integral.RankTwo
open ClassicalData
local instance b2EquivRootDecidableEq : DecidableEq (BRoot 2) := Classical.decEq _
local instance b2EquivBaseDecidableEq : DecidableEq (baseB 1).support :=
  inferInstanceAs (DecidableEq {i : BRoot 2 // i ∈ (baseB 1).support})
local instance c2EquivBaseDecidableEq : DecidableEq (baseC 1).support :=
  inferInstanceAs (DecidableEq {i : BRoot 2 // i ∈ (baseC 1).support})
variable (R : Type*) [CommRing R]

def b2c2UnitsEquiv :
    (Matrix ((baseB 1).support ⊕ BRoot 2) ((baseB 1).support ⊕ BRoot 2) R)ˣ ≃*
    (Matrix ((baseC 1).support ⊕ BRoot 2) ((baseC 1).support ⊕ BRoot 2) R)ˣ :=
  Units.mapEquiv (b2c2MatrixEquiv R).toMulEquiv

theorem b2c2UnitsEquiv_raising (k : Fin 2) (t : R) :
    b2c2UnitsEquiv R (raisingRootElement (pairingB 2) (baseB 1) R
      (baseBIndexEquiv 1 (bSimplePermutation k)) t) =
    raisingRootElement (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 k) t := by
  apply Units.ext
  exact b2c2MatrixEquiv_raising R k t

theorem b2c2UnitsEquiv_lowering (k : Fin 2) (t : R) :
    b2c2UnitsEquiv R (loweringRootElement (pairingB 2) (baseB 1) R
      (baseBIndexEquiv 1 (bSimplePermutation k)) t) =
    loweringRootElement (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 k) t := by
  apply Units.ext
  exact b2c2MatrixEquiv_lowering R k t

theorem b2c2UnitsEquiv_generators :
    b2c2UnitsEquiv R '' adjointGenerators (pairingB 2) (baseB 1) R =
      adjointGenerators (pairingC 2) (baseC 1) R := by
  ext g
  constructor
  · rintro ⟨h,hh,rfl⟩
    rcases hh with ⟨i,t,rfl⟩ | ⟨i,t,rfl⟩
    · obtain ⟨k,rfl⟩ := (bSimplePermutation.trans (baseBIndexEquiv 1)).surjective i
      exact Or.inl ⟨baseCIndexEquiv 1 k,t,b2c2UnitsEquiv_raising R k t⟩
    · obtain ⟨k,rfl⟩ := (bSimplePermutation.trans (baseBIndexEquiv 1)).surjective i
      exact Or.inr ⟨baseCIndexEquiv 1 k,t,b2c2UnitsEquiv_lowering R k t⟩
  · rintro (⟨i,t,rfl⟩ | ⟨i,t,rfl⟩)
    · obtain ⟨k,rfl⟩ := (baseCIndexEquiv 1).surjective i
      refine ⟨raisingRootElement (pairingB 2) (baseB 1) R
        (baseBIndexEquiv 1 (bSimplePermutation k)) t,Or.inl ⟨_,t,rfl⟩,?_⟩
      exact b2c2UnitsEquiv_raising R k t
    · obtain ⟨k,rfl⟩ := (baseCIndexEquiv 1).surjective i
      refine ⟨loweringRootElement (pairingB 2) (baseB 1) R
        (baseBIndexEquiv 1 (bSimplePermutation k)) t,Or.inr ⟨_,t,rfl⟩,?_⟩
      exact b2c2UnitsEquiv_lowering R k t

theorem b2c2UnitsEquiv_adjointSubgroup :
    (adjointSubgroup (pairingB 2) (baseB 1) R).map (b2c2UnitsEquiv R).toMonoidHom =
      adjointSubgroup (pairingC 2) (baseC 1) R := by
  simp only [adjointSubgroup, MonoidHom.map_closure]
  exact congrArg Subgroup.closure (b2c2UnitsEquiv_generators R)

/-- Actual matrix-group isomorphism on the pinned swapped simple roots. -/
def b2c2AdjointEquiv : Adjoint (pairingB 2) (baseB 1) R ≃*
    Adjoint (pairingC 2) (baseC 1) R :=
  ((b2c2UnitsEquiv R).subgroupMap (adjointSubgroup (pairingB 2) (baseB 1) R)).trans
    (MulEquiv.subgroupCongr (b2c2UnitsEquiv_adjointSubgroup R))

theorem b2c2AdjointEquiv_X (k : Fin 2) (t : R) :
    b2c2AdjointEquiv R (adjointX (pairingB 2) (baseB 1) R
      (baseBIndexEquiv 1 (bSimplePermutation k)) t) =
    adjointX (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 k) t := by
  apply Subtype.ext
  exact b2c2UnitsEquiv_raising R k t

theorem b2c2AdjointEquiv_Y (k : Fin 2) (t : R) :
    b2c2AdjointEquiv R (adjointY (pairingB 2) (baseB 1) R
      (baseBIndexEquiv 1 (bSimplePermutation k)) t) =
    adjointY (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 k) t := by
  apply Subtype.ext
  exact b2c2UnitsEquiv_lowering R k t

end Atlas.Chevalley.Integral.RankTwo
