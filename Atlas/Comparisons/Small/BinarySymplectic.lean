import Atlas.Comparisons.Exceptional.BinaryDerived
import Mathlib.FieldTheory.Finite.GaloisField

/-! The full six-point comparison, with the previously fixed B2 marking retained. -/
noncomputable section
namespace Atlas.Comparisons.Exceptional

/-- The full C2(2) carrier, not its derived subgroup. -/
def c2BinaryEquivSymmetric : Atlas.Symplectic.PSp 2 (ZMod 2) ≃* Equiv.Perm (Fin 6) :=
  Classical.b2EquivC2.symm.trans Atlas.Orthogonal.b2BinaryEquivSymmetric

@[simp] theorem c2BinaryEquivSymmetric_coherence
    (g : Atlas.Orthogonal.ProjectiveElementary (Atlas.Orthogonal.formB 2 (ZMod 2))) :
    c2BinaryEquivSymmetric (Classical.b2EquivC2 g) =
      Atlas.Orthogonal.b2BinaryEquivSymmetric g := by
  simp [c2BinaryEquivSymmetric]

/-- The full comparison and the already published derived comparison use the same marking. -/
theorem c2BinaryEquivSymmetric_derived
    (g : commutator (Atlas.Symplectic.PSp 2 (ZMod 2))) :
    c2BinaryEquivSymmetric g.val = (c2BinaryDerivedEquivAlt6 g).val := by
  obtain ⟨h, rfl⟩ := b2BinaryDerivedEquivC2Derived.surjective g
  rw [c2BinaryDerivedEquivAlt6_coherence, b2BinaryDerivedEquivC2Derived_coe,
    c2BinaryEquivSymmetric_coherence]
  rfl

variable {F : Type*} [Field F] [Finite F]
def binaryFieldEquiv (hF : Nat.card F = 2) : F ≃+* ZMod 2 := by
  letI := Fintype.ofFinite F
  apply FiniteField.ringEquivOfCardEq
  simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF

def c2Card2EquivSymmetric (hF : Nat.card F = 2) :
    Atlas.Symplectic.PSp 2 F ≃* Equiv.Perm (Fin 6) :=
  (Atlas.Symplectic.fieldEquivPSp (binaryFieldEquiv hF)).trans c2BinaryEquivSymmetric

def b2Card2EquivSymmetric (hF : Nat.card F = 2) :
    Atlas.Orthogonal.ProjectiveElementary (Atlas.Orthogonal.formB 2 F) ≃*
      Equiv.Perm (Fin 6) :=
  Classical.b2EquivC2.trans (c2Card2EquivSymmetric hF)
end Atlas.Comparisons.Exceptional
