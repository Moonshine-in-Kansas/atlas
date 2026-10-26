import Atlas.LinearGroups.F4.Radical
import Atlas.LinearGroups.F4.RootGeneratedElements

/-! The explicit local subgroup lies in the ambient derived group,
without assuming that roots generate the full Albert stabilizer. -/
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

theorem halfRoot_mem_commutator (i : Fin 8) (t : F) :
    halfRoot i t ∈ commutator (Model F) := by
  unfold halfRoot
  exact shortRoot_mem_commutator _ _ _

theorem halfWord_mem_commutator (t : Fin 8→F) :
    halfWord t ∈ commutator (Model F) := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hg
  exact halfRoot_mem_commutator i (t i)

theorem radicalSubgroup_le_commutator :
    radicalSubgroup (F:=F) ≤ commutator (Model F) := by
  rintro g ⟨p,rfl⟩
  exact (commutator (Model F)).mul_mem
    (centralSeven_mem_commutator _) (halfWord_mem_commutator _)

theorem radicalSubgroup_le_rootGenerated :
    radicalSubgroup (F:=F) ≤ rootGenerated := by
  rintro g ⟨p,rfl⟩
  exact (rootGenerated (F:=F)).mul_mem
    (centralSeven_mem_rootGenerated _) (halfWord_mem_rootGenerated _)

end Atlas.F4
