import Atlas.LinearGroups.F4.RadicalRegular
import Atlas.LinearGroups.F4.OppositeCellParabolicAction
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Reduction of the full parabolic to its actual opposite-pair stabilizer.
No Levi order or normality assertion is assumed in this reduction. -/
noncomputable section
set_option maxRecDepth 4096
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def radicalParabolicHom : RadicalParameters F →* parabolicPointStabilizer (F:=F) where
  toFun p := ⟨radicalElement p,radicalSubgroup_le_parabolic ⟨p,rfl⟩⟩
  map_one' := Subtype.ext radicalElement_one
  map_mul' p q := Subtype.ext (radicalElement_mul p q)

theorem radicalParabolic_character (p : RadicalParameters F) :
    parabolicLineCharacter (radicalParabolicHom p)=1 := by
  apply Units.ext
  have h := parabolicLineCharacter_C7 (radicalParabolicHom p)
    (oppositeBaseCell (F:=F)).val
  have hc : ((radicalParabolicHom p).val.val (oppositeBaseCell (F:=F)).val).2 2 7=1 :=
    (radicalOpposite p (oppositeBaseCell (F:=F))).prop.2.2
  rw [hc,(oppositeBaseCell (F:=F)).prop.2.2,mul_one] at h
  exact h

theorem radicalParabolic_smul (p : RadicalParameters F) (x : OppositeCell F) :
    radicalParabolicHom p • x=radicalOpposite p x := by
  apply Subtype.ext
  rw [oppositeCellParabolicAction_val,radicalParabolic_character]
  simp only [Units.val_one,one_smul]
  rfl

instance oppositeCellParabolic_pretransitive :
    MulAction.IsPretransitive (parabolicPointStabilizer (F:=F)) (OppositeCell F) where
  exists_smul_eq x y := by
    refine ⟨radicalParabolicHom (radicalBetween x y),?_⟩
    rw [radicalParabolic_smul,radicalBetween_apply]

def oppositePairStabilizer : Subgroup (parabolicPointStabilizer (F:=F)) :=
  MulAction.stabilizer _ (oppositeBaseCell (F:=F))

theorem parabolic_factorization (g : parabolicPointStabilizer (F:=F)) :
    ∃ p : RadicalParameters F, ∃ l : oppositePairStabilizer (F:=F),
      g=radicalParabolicHom p*l.val := by
  let p := radicalBetween (oppositeBaseCell (F:=F)) (g • (oppositeBaseCell (F:=F)))
  have hp : radicalParabolicHom p • (oppositeBaseCell (F:=F))=g • (oppositeBaseCell (F:=F)) := by
    rw [radicalParabolic_smul]
    exact radicalBetween_apply _ _
  let l := (radicalParabolicHom p)⁻¹*g
  have hl : l∈oppositePairStabilizer (F:=F) := by
    change ((radicalParabolicHom p)⁻¹*g) • (oppositeBaseCell (F:=F))=(oppositeBaseCell (F:=F))
    rw [mul_smul,←hp,inv_smul_smul]
  refine ⟨p,⟨l,hl⟩,?_⟩
  dsimp [l]
  simp


def parabolicDecompositionMap (x : RadicalParameters F × oppositePairStabilizer (F:=F)) :
    parabolicPointStabilizer (F:=F) := radicalParabolicHom x.1*x.2.val

theorem parabolicDecompositionMap_bijective :
    Function.Bijective (parabolicDecompositionMap (F:=F)) := by
  constructor
  · rintro ⟨p,l⟩ ⟨q,k⟩ he
    have h := congrArg (fun g : parabolicPointStabilizer (F:=F) =>
      g • (oppositeBaseCell (F:=F))) he
    change (radicalParabolicHom p*l.val) • (oppositeBaseCell (F:=F))=
      (radicalParabolicHom q*k.val) • (oppositeBaseCell (F:=F)) at h
    have hl : l.val • (oppositeBaseCell (F:=F))=(oppositeBaseCell (F:=F)) := l.prop
    have hk : k.val • (oppositeBaseCell (F:=F))=(oppositeBaseCell (F:=F)) := k.prop
    rw [mul_smul,mul_smul,hl,hk,radicalParabolic_smul,radicalParabolic_smul] at h
    have hp := radicalOpposite_parameter_injective (oppositeBaseCell (F:=F)) h
    subst q
    refine Prod.ext rfl ?_
    apply Subtype.ext
    exact mul_left_cancel he
  · intro g
    obtain ⟨p,l,he⟩ := parabolic_factorization g
    exact ⟨(p,l),he.symm⟩

/-- Unique radical/opposite-pair factors in the actual full parabolic. -/
def parabolicDecompositionEquiv :
    RadicalParameters F × oppositePairStabilizer (F:=F) ≃ parabolicPointStabilizer (F:=F) :=
  Equiv.ofBijective parabolicDecompositionMap parabolicDecompositionMap_bijective

theorem card_parabolic_eq_cell_mul_pair [Finite F] :
    Nat.card (parabolicPointStabilizer (F:=F))=
      Nat.card F^15*Nat.card (oppositePairStabilizer (F:=F)) := by
  rw [←Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    (parabolicPointStabilizer (F:=F)) (oppositeBaseCell (F:=F))),Nat.card_prod]
  change Nat.card (MulAction.orbit (parabolicPointStabilizer (F:=F)) (oppositeBaseCell (F:=F)))*_=_
  rw [MulAction.orbit_eq_univ,Nat.card_congr (Equiv.Set.univ (OppositeCell F)),oppositeCell_card]
  rfl

end Atlas.F4
