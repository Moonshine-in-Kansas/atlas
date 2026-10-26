import Atlas.Rudvalis.LatticeCrossCount
import Atlas.Rudvalis.LatticeCoordinateOrbit
import Atlas.Rudvalis.FourMinimumOrbit
import Mathlib.GroupTheory.GroupAction.SubMulAction

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem integerLift_monomial (g : SignedCoordinates Coordinate) (w : QuaternaryWord)
    (hw : ∀i,w i≠2) : integerLift (monomialHom g w)=integerMonomial g (integerLift w) := by
  have h : ∀a : ZMod 4,∀b : Bit,a≠2 →
      integerRepresentative (signedScalar b a)=liftedSign b (integerRepresentative a) := by decide +kernel
  funext i
  exact h _ _ (hw _)

theorem minimumWordShellLift_equivariant (g : codeGroup) (w : MinimumWords) :
    minimumWordShellLift (g • w)=g • minimumWordShellLift w := by
  apply Subtype.ext
  apply Subtype.ext
  change halfCoordinates (integerLift (monomialHom g.val w.val.val))=
    rationalMonomialHom g.val (halfCoordinates (integerLift w.val.val))
  rw [rationalMonomial_half,integerLift_monomial _ _ (quaternary_minimum_no_twos _ w.val.prop w.prop)]

def fourMinimumWord (w : FourMinimumWords) : MinimumWords := ⟨w.val,w.prop.1⟩
def heavyMinimumWord (w : HeavyMinimumWords) : MinimumWords := ⟨w.val,w.prop.1⟩

noncomputable def coordinateShellPiece : SubMulAction codeGroup MinimalShell where
  carrier := Set.range coordinateShellLift
  smul_mem' g := by
    rintro _ ⟨a,rfl⟩
    obtain ⟨b,hb⟩ := coordinateShell_stable g a
    exact ⟨b,Subtype.ext (Subtype.ext hb.symm)⟩

noncomputable def fourShellPiece : SubMulAction codeGroup MinimalShell where
  carrier := Set.range (fun w : FourMinimumWords => minimumWordShellLift (fourMinimumWord w))
  smul_mem' g := by
    rintro _ ⟨w,rfl⟩
    let u : MinimumWords := g • fourMinimumWord w
    have hu : admissibleFourSupport (reduce u.val.val) := by
      rcases quaternary_minimum_support_cases u.val.val u.val.prop u.prop with h|h
      · exact h
      · have hc := codeAction_activeBlocks_card g w.val.val
        change (activeBlocks (reduce u.val.val)).card=(activeBlocks (reduce w.val.val)).card at hc
        rw [heavy_activeBlocks_card _ h,four_minimum_activeBlocks_card _ w.val.prop w.prop.1 w.prop.2] at hc
        omega
    exact ⟨⟨u.val,u.prop,hu⟩,minimumWordShellLift_equivariant g (fourMinimumWord w)⟩

noncomputable def heavyShellPiece : SubMulAction codeGroup MinimalShell where
  carrier := Set.range (fun w : HeavyMinimumWords => minimumWordShellLift (heavyMinimumWord w))
  smul_mem' g := by
    rintro _ ⟨w,rfl⟩
    let u : MinimumWords := g • heavyMinimumWord w
    have hu : hasNonzeroQuadraticPart (reduce u.val.val) := by
      rcases quaternary_minimum_support_cases u.val.val u.val.prop u.prop with h|h
      · have hc := codeAction_activeBlocks_card g w.val.val
        change (activeBlocks (reduce u.val.val)).card=(activeBlocks (reduce w.val.val)).card at hc
        rw [heavy_activeBlocks_card _ w.prop.2,four_minimum_activeBlocks_card _ u.val.prop u.prop h] at hc
        omega
      · exact h
    exact ⟨⟨u.val,u.prop,hu⟩,minimumWordShellLift_equivariant g (heavyMinimumWord w)⟩

theorem coordinateShellPiece_card : Nat.card coordinateShellPiece=112 := by
  change Nat.card (Set.range coordinateShellLift)=112
  rw [←Nat.card_congr (Equiv.ofInjective coordinateShellLift coordinateShellLift_injective)]
  norm_num [Nat.card_eq_fintype_card]

theorem fourShellPiece_card : Nat.card fourShellPiece=1792 := by
  have hi : Function.Injective (fun w : FourMinimumWords => minimumWordShellLift (fourMinimumWord w)) := by
    intro a b h
    exact Subtype.ext (congrArg (fun u : MinimumWords => u.val) (minimumWordShellLift_injective h))
  change Nat.card (Set.range (fun w : FourMinimumWords => minimumWordShellLift (fourMinimumWord w)))=1792
  rw [←Nat.card_congr (Equiv.ofInjective _ hi)]
  exact four_minimum_words_card

theorem heavyShellPiece_card : Nat.card heavyShellPiece=14336 := by
  have hi : Function.Injective (fun w : HeavyMinimumWords => minimumWordShellLift (heavyMinimumWord w)) := by
    intro a b h
    exact Subtype.ext (congrArg (fun u : MinimumWords => u.val) (minimumWordShellLift_injective h))
  change Nat.card (Set.range (fun w : HeavyMinimumWords => minimumWordShellLift (heavyMinimumWord w)))=14336
  rw [←Nat.card_congr (Equiv.ofInjective _ hi)]
  exact heavy_minimum_words_card

end Atlas.Rudvalis
