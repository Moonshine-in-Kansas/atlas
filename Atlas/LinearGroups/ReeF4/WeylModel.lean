import Atlas.LinearGroups.ReeF4.WeylDihedralMembership
import Atlas.LinearGroups.ReeF4.IntrinsicGroup

/-! The actual dihedral subgroup inside the intrinsic Ree model. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem weylOperator_mem_modelSubgroup (m : ℕ) (g : Fin 2) :
    weylOperator g ∈ modelSubgroup F m := by
  rw [mem_modelSubgroup_iff]
  exact ⟨weylOperator_mem_polynomialStabilizer g,
    weyl_mem_candidatePartialStabilizer (thetaInv F m).toRingHom g⟩

theorem weylSubgroup_le_modelSubgroup (m : ℕ) :
    weylSubgroup (F := F) ≤ modelSubgroup F m := by
  rw [weylSubgroup_eq_closure]
  apply (Subgroup.closure_le (modelSubgroup F m)).mpr
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact weylOperator_mem_modelSubgroup m 0
  · exact weylOperator_mem_modelSubgroup m 1

def modelWeylEmbedding (m : ℕ) : weylSubgroup (F := F) →* Model F m :=
  Subgroup.inclusion (weylSubgroup_le_modelSubgroup m)

theorem modelWeylEmbedding_injective (m : ℕ) :
    Function.Injective (modelWeylEmbedding (F := F) m) := by
  intro g h he
  apply Subtype.ext
  exact congrArg (fun z : Model F m => z.val) he

/-- The intrinsic model is noncommutative even in the binary case. -/
theorem model_noncommutative (m : ℕ) :
    ∃ g h : Model F m, g * h ≠ h * g := by
  let e : DihedralGroup 8 →* Model F m :=
    (modelWeylEmbedding m).comp (weylDihedralEquiv (F := F)).toMonoidHom
  have hi : Function.Injective e :=
    (modelWeylEmbedding_injective m).comp (weylDihedralEquiv (F := F)).injective
  have hn : (DihedralGroup.r (1 : ZMod 8)) * DihedralGroup.sr 0 ≠
      DihedralGroup.sr 0 * DihedralGroup.r 1 := by decide
  refine ⟨e (DihedralGroup.r 1), e (DihedralGroup.sr 0), ?_⟩
  intro h
  apply hn
  apply hi
  simpa only [map_mul] using h

end Atlas.ReeF4
