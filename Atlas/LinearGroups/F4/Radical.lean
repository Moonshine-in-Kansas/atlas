import Atlas.LinearGroups.F4.HalfWordCentral
import Atlas.LinearGroups.F4.OppositeCellTransitivity
import Atlas.LinearGroups.F4.OppositeCellFaithfulness
import Atlas.GroupTheory.BilinearCentralExtension

/-! The actual fifteen-parameter positive radical subgroup. Full-stabilizer
normality is a separate obligation; it is not built into this definition. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def radicalCocycle : (Fin 8→F) →+ (Fin 8→F) →+ (Fin 7→F) where
  toFun t := (halfWordBilinearMap (F:=F) t).toAddMonoidHom
  map_zero' := by ext z; simp
  map_add' t u := by ext z; simp

theorem radicalCocycle_apply (t z : Fin 8→F) :
    radicalCocycle t z=halfWordBilinear t z := halfWordBilinearMap_apply t z

abbrev RadicalParameters (F : Type*) [Field F] :=
  Atlas.GroupTheory.BilinearExtension (radicalCocycle (F:=F))

def radicalElement (p : RadicalParameters F) : Model F :=
  centralSeven (p.central-centralSevenCoordinates ((halfWord p.point).val halfWordBaseVector))*
    halfWord p.point

def radicalOpposite (p : RadicalParameters F) (x : OppositeCell F) : OppositeCell F :=
  centralSevenOpposite
    (p.central-centralSevenCoordinates ((halfWord p.point).val halfWordBaseVector))
    (halfWordOpposite p.point x)

theorem radicalOpposite_val (p : RadicalParameters F) (x : OppositeCell F) :
    (radicalOpposite p x).val=(radicalElement p).val x.val := rfl

theorem radicalOpposite_lower (p : RadicalParameters F) (x : OppositeCell F) :
    oppositeLowerCoordinates (radicalOpposite p x).val=oppositeLowerCoordinates x.val+p.point := by
  change negativeSpinCoordinates (centralSevenApply _ ((halfWord p.point).val x.val))=_
  rw [centralSeven_negative]
  have h := (halfWord_lower p.point x.val).2
  rw [x.prop.2.2] at h
  change oppositeLowerCoordinates ((halfWord p.point).val x.val)=_
  simpa only [mul_one] using h

theorem radicalOpposite_central (p : RadicalParameters F) (x : OppositeCell F) :
    centralSevenCoordinates (radicalOpposite p x).val=centralSevenCoordinates x.val+
      radicalCocycle p.point (oppositeLowerCoordinates x.val)+p.central := by
  change centralSevenCoordinates (centralSevenApply _ ((halfWord p.point).val x.val))=_
  have hc : ((halfWord p.point).val x.val).2 2 7=1 :=
    (halfWord_lower p.point x.val).1.trans x.prop.2.2
  rw [centralSeven_coordinates_chart _ _ hc,
    halfWord_central_chart p.point x.val x.prop.2.2,radicalCocycle_apply]
  abel

theorem radicalOpposite_mul (p q : RadicalParameters F) (x : OppositeCell F) :
    radicalOpposite (p*q) x=radicalOpposite p (radicalOpposite q x) := by
  apply oppositeCell_coordinate_ext
  · rw [radicalOpposite_lower,radicalOpposite_lower,radicalOpposite_lower]
    change _+(p.point+q.point)=(_+q.point)+p.point
    abel
  · rw [radicalOpposite_central,radicalOpposite_central,radicalOpposite_central,
      radicalOpposite_lower]
    change centralSevenCoordinates x.val+
        radicalCocycle (p.point+q.point) (oppositeLowerCoordinates x.val)+
        (p.central+q.central+radicalCocycle p.point q.point) =
      (centralSevenCoordinates x.val+radicalCocycle q.point (oppositeLowerCoordinates x.val)+q.central)+
        radicalCocycle p.point (oppositeLowerCoordinates x.val+q.point)+p.central
    simp only [_root_.map_add,AddMonoidHom.add_apply]
    abel

attribute [local irreducible] radicalElement

theorem radicalElement_mul (p q : RadicalParameters F) :
    radicalElement (p*q)=radicalElement p*radicalElement q := by
  apply oppositeCell_action_ext
  intro x
  have h := congrArg Subtype.val (radicalOpposite_mul p q x)
  rw [radicalOpposite_val,radicalOpposite_val,radicalOpposite_val] at h
  change (radicalElement (p*q)).val x.val =
    (radicalElement p).val ((radicalElement q).val x.val)
  exact h

theorem radicalElement_one : radicalElement (1 : RadicalParameters F)=1 := by
  have h := radicalElement_mul (1 : RadicalParameters F) 1
  have hh : radicalElement (1 : RadicalParameters F)*radicalElement 1=radicalElement 1*1 := by
    simpa using h.symm
  exact mul_left_cancel hh

def radicalHom : RadicalParameters F →* Model F where
  toFun := radicalElement
  map_one' := radicalElement_one
  map_mul' := radicalElement_mul

theorem radicalElement_injective : Function.Injective (radicalElement (F:=F)) := by
  intro p q h
  have he : radicalOpposite p oppositeBaseCell=radicalOpposite q oppositeBaseCell := by
    apply Subtype.ext
    rw [radicalOpposite_val,radicalOpposite_val,h]
  have hl := congrArg (fun x : OppositeCell F=>oppositeLowerCoordinates x.val) he
  have hc := congrArg (fun x : OppositeCell F=>centralSevenCoordinates x.val) he
  rw [radicalOpposite_lower,radicalOpposite_lower] at hl
  rw [radicalOpposite_central,radicalOpposite_central] at hc
  have hb : oppositeLowerCoordinates (oppositeBaseCell (F:=F)).val=0 := by
    rw [oppositeBaseCell_coordinates]
    exact halfWordBaseVector_lower
  rw [hb,map_zero,map_zero] at hc
  apply Atlas.GroupTheory.BilinearExtension.ext
  · exact add_left_cancel hl
  · simpa only [add_zero] using add_left_cancel hc

def radicalSubgroup : Subgroup (Model F) := (radicalHom (F:=F)).range

theorem card_radicalSubgroup [Finite F] : Nat.card (radicalSubgroup (F:=F))=Nat.card F^15 := by
  change Nat.card (Set.range (radicalElement (F:=F)))=_
  rw [Nat.card_range_of_injective radicalElement_injective]
  change Nat.card (Atlas.GroupTheory.BilinearExtension (radicalCocycle (F:=F)))=_
  rw [Atlas.GroupTheory.BilinearExtension.card]
  simp only [Nat.card_fun,Nat.card_fin]
  ring

theorem radicalSubgroup_solvable : Group.IsSolvable (radicalSubgroup (F:=F)) :=
  Group.isSolvable_of_surjective (radicalHom (F:=F)).rangeRestrict_surjective

theorem radicalSubgroup_le_parabolic : radicalSubgroup (F:=F) ≤ parabolicPointStabilizer := by
  rintro g ⟨p,rfl⟩
  change radicalElement p∈parabolicPointStabilizer
  unfold radicalElement
  exact (parabolicPointStabilizer (F:=F)).mul_mem
    (centralSeven_mem_parabolicPointStabilizer _) (halfWord_mem_parabolic _)

end Atlas.F4
