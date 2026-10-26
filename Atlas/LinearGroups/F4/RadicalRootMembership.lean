import Atlas.LinearGroups.F4.Radical
import Atlas.LinearGroups.F4.CentralSevenCommutation

/-! The seven central and eight half-root directions are genuine elements of
the constructed fifteen-parameter subgroup. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

theorem radicalCocycle_single (i : Fin 8) (t : F) (z : Fin 8→F) :
    radicalCocycle (Pi.single i t) z=t • halfRootCentralLinear i z := by
  rw [radicalCocycle_apply]
  simp [halfWordBilinear,Pi.single_apply,halfRootCentralLinear]

theorem radicalElement_central (z : Fin 7→F) :
    radicalElement (⟨0,z⟩ : RadicalParameters F)=centralSeven z := by
  apply oppositeCell_action_ext
  intro x
  have he : radicalOpposite (⟨0,z⟩ : RadicalParameters F) x=centralSevenOpposite z x := by
    apply oppositeCell_coordinate_ext
    · rw [radicalOpposite_lower]
      change oppositeLowerCoordinates x.val+0=oppositeLowerCoordinates ((centralSeven z).val x.val)
      rw [centralSeven_lower,add_zero]
    · rw [radicalOpposite_central]
      change centralSevenCoordinates x.val+radicalCocycle 0 (oppositeLowerCoordinates x.val)+z=
        centralSevenCoordinates ((centralSeven z).val x.val)
      rw [centralSeven_middle z x.val x.prop.2.2]
      simp
  have h := congrArg Subtype.val he
  rw [radicalOpposite_val] at h
  exact h

theorem centralSeven_mem_radical (z : Fin 7→F) : centralSeven z∈radicalSubgroup :=
  ⟨⟨0,z⟩,radicalElement_central z⟩

theorem radicalElement_halfRoot (i : Fin 8) (t : F) :
    radicalElement (⟨Pi.single i t,0⟩ : RadicalParameters F)=halfRoot i t := by
  apply oppositeCell_action_ext
  intro x
  have he : radicalOpposite (⟨Pi.single i t,0⟩ : RadicalParameters F) x=halfRootOpposite i t x := by
    apply oppositeCell_coordinate_ext
    · rw [radicalOpposite_lower]
      change oppositeLowerCoordinates x.val+Pi.single i t=
        oppositeLowerCoordinates ((halfRoot i t).val x.val)
      rw [(halfRoot_lower i t x.val).2,x.prop.2.2,mul_one]
    · rw [radicalOpposite_central]
      change centralSevenCoordinates x.val+radicalCocycle (Pi.single i t)
        (oppositeLowerCoordinates x.val)+0=centralSevenCoordinates ((halfRoot i t).val x.val)
      rw [radicalCocycle_single,halfRoot_central,add_zero]
      rfl
  have h := congrArg Subtype.val he
  rw [radicalOpposite_val] at h
  exact h

theorem halfRoot_mem_radical (i : Fin 8) (t : F) : halfRoot i t∈radicalSubgroup :=
  ⟨⟨Pi.single i t,0⟩,radicalElement_halfRoot i t⟩

end Atlas.F4
