import Atlas.LinearGroups.F4.Perfect
import Atlas.LinearGroups.F4.RadicalNormal

/-! The actual local solvable subgroup normally generates the full Albert group. -/
namespace Atlas.F4
variable {F : Type*} [Field F] [Finite F]

theorem radical_normalClosure_eq_top :
    Subgroup.normalClosure (radicalSubgroup (F:=F) : Set (Model F)) = ⊤ := by
  apply normal_eq_top_of_contains_radical
  exact Subgroup.subset_normalClosure

theorem radical_normal_in_pointStabilizer :
    ((radicalSubgroup (F:=F)).subgroupOf
      (MulAction.stabilizer (Model F) (parabolicPoint (F := F)))).Normal := by
  have he : (radicalSubgroup (F:=F)).subgroupOf parabolicPointStabilizer = parabolicRadical := by
    ext g
    exact (parabolicRadical_mem_iff g).symm
  change ((radicalSubgroup (F:=F)).subgroupOf parabolicPointStabilizer).Normal
  rw [he]
  exact parabolicRadical_normal

end Atlas.F4
