import Atlas.LinearGroups.Orthogonal.Minus.ReflectionGeneration
import Atlas.LinearGroups.Orthogonal.Minus.IntrinsicOdd
import Atlas.LinearGroups.Orthogonal.DicksonEvenReflectionKernel

/-! Full residual-rank character and intrinsic characteristic-two Omega. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def fullDickson (hdeg : Module.finrank F K = 2) (n : ℕ) :
    O hdeg (n+2) →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (dicksonValue (form hdeg (n+2)) g)
  map_one' := dicksonValue_one _
  map_mul' g h := by
    apply dicksonParity_mul_of_mem_reflectionSubgroup _ (polar_nondegenerate hdeg _) g _ h
    rw [reflectionSubgroup_eq_top hdeg n]
    trivial

theorem fullDickson_surjective (hdeg : Module.finrank F K = 2) (n : ℕ) :
    Function.Surjective (fullDickson hdeg n) := by
  have ha : form hdeg (n+2) (0,1) ≠ 0 := by
    simp only [form_apply,map_zero,zero_add,← normForm_apply hdeg]
    exact fun h => one_ne_zero ((normForm_eq_zero_iff hdeg 1).mp h)
  intro x
  obtain ⟨g,hg⟩ := reflectionDicksonCharacter_surjective (form hdeg (n+2))
    (polar_nondegenerate hdeg _) (0,1) ha x
  exact ⟨g.val,hg⟩

theorem fullDickson_kernel_evenReflection (hdeg : Module.finrank F K = 2) (n : ℕ) :
    (fullDickson hdeg n).ker = evenReflectionSubgroup (form hdeg (n+2)) := by
  ext g
  rw [mem_evenReflection_iff _ (polar_nondegenerate hdeg _)]
  have hg : g ∈ reflectionSubgroup (form hdeg (n+2)) := by
    rw [reflectionSubgroup_eq_top hdeg n]
    trivial
  change dicksonValue (form hdeg (n+2)) g = 0 ↔
    g ∈ reflectionSubgroup (form hdeg (n+2)) ∧ dicksonValue (form hdeg (n+2)) g = 0
  exact ⟨fun hz => ⟨hg,hz⟩,fun h => h.2⟩

theorem elementary_le_evenReflection (hdeg : Module.finrank F K = 2) (n : ℕ) :
    E hdeg (n+2) ≤ evenReflectionSubgroup (form hdeg (n+2)) := by
  intro g hg
  apply (mem_evenReflection_iff _ (polar_nondegenerate hdeg _) g).mpr
  constructor
  · rw [reflectionSubgroup_eq_top hdeg n]; trivial
  · apply dicksonValue_elementary_stable _ (polar_nondegenerate hdeg _) _ g hg
    rw [vector_finrank hdeg]
    omega

theorem fullDickson_kernel_elementary [CharP F 2] [PerfectRing F 2]
    (hdeg : Module.finrank F K = 2) (n : ℕ) :
    (fullDickson hdeg n).ker = E hdeg (n+2) := by
  rw [fullDickson_kernel_evenReflection]
  exact le_antisymm (evenReflection_le_elementary hdeg n) (elementary_le_evenReflection hdeg n)

theorem elementary_index_even [CharP F 2] [PerfectRing F 2]
    (hdeg : Module.finrank F K = 2) (n : ℕ) : (E hdeg (n+2)).index = 2 := by
  rw [← fullDickson_kernel_elementary hdeg n]
  rw [Subgroup.index_ker]
  rw [MonoidHom.range_eq_top.mpr (fullDickson_surjective hdeg n)]
  rw [Nat.card_congr Subgroup.topEquiv.toEquiv]
  change Nat.card (ZMod 2) = 2
  simp
end Atlas.Orthogonal.Minus
