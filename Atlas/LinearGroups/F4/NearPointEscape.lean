import Atlas.LinearGroups.F4.NearPointReduction
import Atlas.LinearGroups.F4.CanonicalNearEscape
import Atlas.LinearGroups.F4.PointOpposition
import Atlas.GroupTheory.PrimitivePointChainTransport

/-! The two-step canonical escape extends to every near point by actual
parabolic root reduction. No numerical group order is used. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
open scoped LinearAlgebra.Projectivization
variable {F : Type*} [Field F]

theorem point_eq_parabolic_of_nearSpin_zero (x : WhiteZeroPoints F)
    (hx : x.val.rep∈parabolicImageZero (F:=F))
    (hv : nearSpinCoordinates x.val.rep=0) : x=parabolicPoint := by
  have he := nearVector_reconstruction x.val.rep hx
  rw [hv] at he
  have hz (c : F) : nearVector c (0 : Fin 8→F)=c • parabolicVector := by
    simp [nearVector,upperSpinEmbed]
  rw [hz] at he
  apply Subtype.ext
  change x.val=Projectivization.mk F parabolicVector _
  rw [←Projectivization.mk_rep x.val,Projectivization.mk_eq_mk_iff']
  exact ⟨x.val.rep.2 2 0,he⟩

/-- Transitivity of the actual parabolic on the near points other than C₀. -/
theorem nearPoint_parabolic_to_base (x : WhiteZeroPoints F)
    (hx : x.val.rep∈parabolicImageZero (F:=F)) (hne : x≠parabolicPoint) :
    ∃ g : parabolicPointStabilizer (F:=F), g.val • x=basePoint F := by
  have hv : nearSpinCoordinates x.val.rep≠0 := by
    intro h
    exact hne (point_eq_parabolic_of_nearSpin_zero x hx h)
  obtain ⟨g,d,hd,hg⟩ := nearVector_parabolic_reduce (x.val.rep.2 2 0)
    (nearSpinCoordinates x.val.rep) hv ((imageZero_rankOne_iff x.val.rep hx).mp x.prop.2)
  rw [nearVector_reconstruction x.val.rep hx] at hg
  refine ⟨g,Subtype.ext ?_⟩
  change g.val.val • x.val=Projectivization.mk F baseVector _
  rw [←Projectivization.mk_rep x.val,Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff']
  exact ⟨d,hg.symm⟩

/-- Every nontrivial point in the intrinsic near nine-space admits a finite
stabilizer-move chain to a point opposite the marked point. -/
theorem nearPoint_stabilizer_chain_escape (x : WhiteZeroPoints F)
    (hx : x.val.rep∈parabolicImageZero (F:=F)) (hne : x≠parabolicPoint) :
    ∃ z : WhiteZeroPoints F,
      Atlas.GroupTheory.StabilizerMoveChain (Model F) parabolicPoint x z ∧
        PointsOpposite parabolicPoint z := by
  obtain ⟨g,hg⟩ := nearPoint_parabolic_to_base x hx hne
  obtain ⟨z,hz,hop⟩ := canonical_near_stabilizer_chain_escape (F:=F)
  have hp : g.val⁻¹ • (parabolicPoint (F:=F))=parabolicPoint := by
    have hfix : g.val • (parabolicPoint (F:=F))=parabolicPoint := g.prop
    rw [←hfix,inv_smul_smul]
    exact hfix.symm
  have hb : g.val⁻¹ • basePoint F=x := by
    rw [←hg,inv_smul_smul]
  refine ⟨g.val⁻¹ • z,?_,?_⟩
  · have h := Atlas.GroupTheory.stabilizerMoveChain_smul g.val⁻¹ hz
    simpa only [hp,hb] using h
  · have h := (pointsOpposite_smul_iff g.val⁻¹ parabolicPoint z).mpr
      ((pointsOpposite_parabolic_iff z).mpr hop)
    simpa only [hp] using h

end Atlas.F4
