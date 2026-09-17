import Atlas.Fischer.RootRayClassInterface
import Atlas.Algebra.InvolutiveParityGeneration

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The original algebra reflections, now viewed inside their generated subgroup. -/
def displayedAlgebraRootElement (t : ReflectingRootParameter) : rootGeneratedAlgebraGroup :=
  ⟨displayedRootAutomorphism t,displayedRootAutomorphism_mem t⟩

def rootGeneratedAlgebraParity : rootGeneratedAlgebraGroup →* Multiplicative Bit :=
  semilinearAlgebraParityHom.comp rootGeneratedAlgebraGroup.subtype

theorem displayedAlgebraRootElement_parity (t : ReflectingRootParameter) :
    rootGeneratedAlgebraParity (displayedAlgebraRootElement t)=Multiplicative.ofAdd (1 : Bit) := by
  change Multiplicative.ofAdd (semilinearAlgebraParity (displayedRootAutomorphism t))=_
  rw [show semilinearAlgebraParity (displayedRootAutomorphism t)=1 from
    rootAlgebraAutomorphism_parity _ (reflectingRootParameter_isReflectingRoot t).1.1
      (reflectingRootParameter_isReflectingRoot t).1.2 (reflectingRootParameter_isReflectingRoot t).2.1]

theorem displayedAlgebraRootElement_mul_self (t : ReflectingRootParameter) :
    displayedAlgebraRootElement t * displayedAlgebraRootElement t=1 := by
  apply Subtype.ext
  exact (pow_two (displayedRootAutomorphism t)).symm.trans (displayedRootAutomorphism_square t)

theorem displayedAlgebraRootElement_generates :
    Subgroup.closure (Set.range displayedAlgebraRootElement)=⊤ := by
  have he : Set.range displayedAlgebraRootElement =
      rootGeneratedAlgebraGroup.subtype ⁻¹' Set.range displayedRootAutomorphism := by
    ext g
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,hi⟩
      exact ⟨i,Subtype.ext hi⟩
  rw [he]
  exact Subgroup.closure_preimage_eq_top (Set.range displayedRootAutomorphism)

/-- The positive algebra subgroup is exactly the even-word subgroup. -/
theorem rootGeneratedAlgebraParity_kernel_pairs : rootGeneratedAlgebraParity.ker =
    Subgroup.closure (Set.range (fun ij : ReflectingRootParameter × ReflectingRootParameter =>
      displayedAlgebraRootElement ij.1 * displayedAlgebraRootElement ij.2)) :=
  Atlas.Algebra.involutive_parity_kernel_generated_pairs displayedAlgebraRootElement
    (.inl (Classical.arbitrary Omega)) displayedAlgebraRootElement_mul_self rootGeneratedAlgebraParity
    displayedAlgebraRootElement_parity displayedAlgebraRootElement_generates

theorem rootGeneratedAlgebraParity_surjective : Function.Surjective rootGeneratedAlgebraParity := by
  intro b
  have hv : ∀ a : Multiplicative Bit, a=1 ∨ a=Multiplicative.ofAdd (1 : Bit) := by decide
  rcases hv b with rfl | rfl
  · exact ⟨1,rootGeneratedAlgebraParity.map_one⟩
  · exact ⟨displayedAlgebraRootElement (.inl (Classical.arbitrary Omega)),displayedAlgebraRootElement_parity _⟩

end Atlas.Fischer
