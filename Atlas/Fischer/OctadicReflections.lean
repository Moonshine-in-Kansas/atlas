import Atlas.Fischer.OctadBlockAssembly
import Atlas.Fischer.OctadDuadBlockPackage
import Atlas.Fischer.OctadTetradBlockPackage
import Atlas.Fischer.OctadicAntiunitaryTransport
import Atlas.Fischer.RootMapEquivalence

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Full antiunitarity is assembled from the actual 9, 46, 16 and 8 blocks. -/
theorem octadicRoot_zero_antiunitary {O : Octad} (Q : OctadCalibration O) :
    RootMapAntiunitary (octadicRoot Q 0) := by
  apply rootMap_octadic_antiunitary_of_local_blocks Q
  · intro S hSO hS
    rcases hS with hS | hS
    · exact rootMap_octadic_duad_block_invariant Q S hSO hS
    · exact rootMap_octadic_tetrad_block_invariant Q S hSO hS
  · intro S hSO hS
    rcases hS with hS | hS
    · exact rootMap_octadic_duad_block_antiunitary Q S hSO hS
    · exact rootMap_octadic_tetrad_block_antiunitary Q S hSO hS

theorem octadicRoot_antiunitary {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) : RootMapAntiunitary (octadicRoot Q χ) :=
  octadicRoot_antiunitary_of_zero Q (octadicRoot_zero_antiunitary Q) χ

theorem octadicRoot_involutive {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) : Function.Involutive (rootMap (octadicRoot Q χ)) :=
  rootMap_involutive_of_antiunitary _ (octadicRoot_antiunitary Q χ)

/-- The actual octadic reflection as an invertible conjugate-linear map.
Multiplicativity is a separate subsequent theorem. -/
def octadicReflection {O : Octad} (Q : OctadCalibration O) (χ : OctadicCharacter O) :
    Coordinates ≃ₛₗ[starRingEnd Scalar] Coordinates :=
  rootMapEquivalence (octadicRoot Q χ) (octadicRoot_antiunitary Q χ)

theorem octadicReflection_apply {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (x : Coordinates) :
    octadicReflection Q χ x = rootMap (octadicRoot Q χ) x := rfl

theorem octadicReflection_hermitian {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (x y : Coordinates) :
    hermitian (octadicReflection Q χ x) (octadicReflection Q χ y) =
      star (hermitian x y) := octadicRoot_antiunitary Q χ x y

theorem octadicReflection_involutive {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) : Function.Involutive (octadicReflection Q χ) :=
  octadicRoot_involutive Q χ

/-- The complete local root-and-reflection assertion, without a multiplicativity premise. -/
theorem octadicRoot_reflection_package {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) :
    IsRoot (octadicRoot Q χ) ∧ RootMapAntiunitary (octadicRoot Q χ) ∧
      Function.Involutive (rootMap (octadicRoot Q χ)) :=
  ⟨octadicRoot_isRoot Q χ, octadicRoot_antiunitary Q χ, octadicRoot_involutive Q χ⟩

end Atlas.Fischer
