import Atlas.LinearGroups.Orthogonal.StableReflectionGenerationD
import Atlas.LinearGroups.Orthogonal.EvenDReflectionIdentification

/-! # The full intrinsic Dickson character of split D in stable rank

The character is defined by the rank of the actual residual linear map. Its
multiplicativity follows from proved full reflection generation. Over a perfect
field of characteristic two its kernel is exactly the actual elementary group.
-/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F]

/-- Full-group additivity of intrinsic residual parity in split rank at least three. -/
theorem dicksonValue_mul_D_stable (n : ℕ) (g h : O_DPlus (n + 3) F) :
    dicksonValue (formD (n + 3) F) (g * h) =
      dicksonValue (formD (n + 3) F) g + dicksonValue (formD (n + 3) F) h := by
  apply dicksonParity_mul_of_mem_reflectionSubgroup _ polarD_nondegenerate g _ h
  rw [reflectionSubgroupD_eq_top_stable]
  trivial

/-- The Dickson character on the full, actual orthogonal group, not a reflection image. -/
def fullDicksonD (n : ℕ) : O_DPlus (n + 3) F →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (dicksonValue (formD (n + 3) F) g)
  map_one' := dicksonValue_one _
  map_mul' g h := dicksonValue_mul_D_stable n g h

@[simp] theorem fullDicksonD_value (n : ℕ) (g : O_DPlus (n + 3) F) :
    (fullDicksonD n g).toAdd = dicksonValue (formD (n + 3) F) g := rfl

/-- The full character restricts to the previously certified reflection character. -/
theorem fullDicksonD_restrict_reflections (n : ℕ)
    (g : reflectionSubgroup (formD (n + 3) F)) :
    fullDicksonD n g.val = splitDReflectionCharacter g := rfl

/-- An actual hyperbolic exchange has nontrivial Dickson value. -/
theorem fullDicksonD_exchange (n : ℕ) (i : Fin (n + 3)) :
    fullDicksonD n (splitDExchangeElement (F := F) i) = Multiplicative.ofAdd 1 := by
  apply Multiplicative.toAdd.injective
  exact dicksonValue_splitDExchange i

/-- Surjectivity is witnessed by the identity and an actual hyperbolic exchange. -/
theorem fullDicksonD_surjective (n : ℕ) : Function.Surjective (fullDicksonD (F := F) n) := by
  intro x
  obtain ⟨g,hg⟩ := splitDReflectionCharacter_surjective (n := n + 3) (F := F) (by omega) x
  exact ⟨g.val,hg⟩

/-- In every characteristic the full character kernel is the normal subgroup
of actual even reflection products. -/
theorem fullDicksonD_kernel_evenReflection (n : ℕ) :
    (fullDicksonD (F := F) n).ker = evenReflectionSubgroup (formD (n + 3) F) := by
  ext g
  rw [mem_evenReflection_iff _ polarD_nondegenerate]
  have hg : g ∈ reflectionSubgroup (formD (n + 3) F) := by
    rw [reflectionSubgroupD_eq_top_stable]
    trivial
  change dicksonValue (formD (n + 3) F) g = 0 ↔
    g ∈ reflectionSubgroup (formD (n + 3) F) ∧ dicksonValue (formD (n + 3) F) g = 0
  exact ⟨fun hz => ⟨hg,hz⟩,fun h => h.2⟩

/-- The intrinsic Dickson kernel is the actual elementary split-D group over a
perfect field of characteristic two. -/
theorem fullDicksonD_kernel_elementary [CharP F 2] [PerfectRing F 2] (n : ℕ) :
    (fullDicksonD (F := F) n).ker = elementarySubgroup (formD (n + 3) F) := by
  rw [fullDicksonD_kernel_evenReflection, evenReflectionD_eq_elementary]

/-- Exact membership characterization for the prescribed characteristic-two model. -/
theorem mem_elementaryD_iff_dickson_zero [CharP F 2] [PerfectRing F 2]
    (n : ℕ) (g : O_DPlus (n + 3) F) :
    g ∈ elementarySubgroup (formD (n + 3) F) ↔ dicksonValue (formD (n + 3) F) g = 0 := by
  rw [← fullDicksonD_kernel_elementary]
  rfl

end Atlas.Orthogonal
