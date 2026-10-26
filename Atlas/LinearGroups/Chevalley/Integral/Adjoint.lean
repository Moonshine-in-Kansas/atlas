import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Semisimple

/-! # Integral Geck operators and coefficient reduction

The source root datum lives over ℤ. Reduction of its integral matrices makes
sense over any commutative ring, including characteristics two and three.
These are raising/lowering operators, not yet invertible root-group elements:
integral divided powers and the exponential identities remain separate obligations.
-/

noncomputable section
namespace Atlas.Chevalley.Integral

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Geck's raising matrix on the integral adjoint module. -/
abbrev raising (i : b.support) := RootPairing.GeckConstruction.e i

/-- Geck's lowering matrix on the integral adjoint module. -/
abbrev lowering (i : b.support) := RootPairing.GeckConstruction.f i

variable (R : Type*) [CommRing R]

/-- Coefficient reduction uses no division in the target ring. -/
def raisingOver (i : b.support) : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  (raising P b i).map (Int.castRingHom R)

/-- Coefficient reduction uses no division in the target ring. -/
def loweringOver (i : b.support) : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  (lowering P b i).map (Int.castRingHom R)

theorem raisingOver_nilpotent (i : b.support) : IsNilpotent (raisingOver P b R i) := by
  classical
  exact (RootPairing.GeckConstruction.isNilpotent_e i).map
    (Int.castRingHom R).mapMatrix

theorem loweringOver_nilpotent (i : b.support) : IsNilpotent (loweringOver P b R i) := by
  classical
  exact (RootPairing.GeckConstruction.isNilpotent_f i).map
    (Int.castRingHom R).mapMatrix

variable {R} {S : Type*} [CommRing S]

omit [DecidableEq ι] [P.IsReduced] in
theorem raisingOver_map (φ : R →+* S) (i : b.support) :
    (raisingOver P b R i).map φ = raisingOver P b S i := by
  ext j k
  simp [raisingOver]

omit [DecidableEq ι] [P.IsReduced] in
theorem loweringOver_map (φ : R →+* S) (i : b.support) :
    (loweringOver P b R i).map φ = loweringOver P b S i := by
  ext j k
  simp [loweringOver]

end Atlas.Chevalley.Integral
