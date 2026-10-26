import Atlas.Rudvalis.CodeRowExact
import Atlas.Rudvalis.CoordinateLocalOrbits
import Atlas.Rudvalis.LocalTransitivity

namespace Atlas.Rudvalis

 theorem codeRowKernel_coordinate_translation (g : codeRowKernel) :
    ∃B : BinaryMatrix,g.val.val.right=coordinateTranslation B := by
  obtain ⟨B,hB⟩ := (codeRowTranslationHom g).prop
  refine ⟨B.toAdd,?_⟩
  exact (congrArg Subtype.val hB).symm

 theorem codeRowKernel_translation_lift (B : BinaryMatrix) :
    ∃g : codeRowKernel,g.val.val.right=coordinateTranslation B := by
  let t : binaryTranslationSubgroup :=
    ⟨coordinateTranslationHom (Multiplicative.ofAdd B),⟨Multiplicative.ofAdd B,rfl⟩⟩
  obtain ⟨g,hg⟩ := codeRowTranslationHom_surjective t
  exact ⟨g,congrArg (fun t : binaryTranslationSubgroup=>t.val.val) hg⟩

 theorem codeRowKernel_coordinate_orbit (p : Point) (x : E) :
    MulAction.orbit codeRowKernel (coordinateCross (p,x))=coordinateRowFrame p := by
  ext c
  constructor
  · intro hc
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hc
    obtain ⟨B,hB⟩ := codeRowKernel_coordinate_translation g
    change g.val • coordinateCross (p,x)∈coordinateRowFrame p
    rw [coordinateCross_action,hB]
    exact ⟨x+matrixAt B p.val,rfl⟩
  · rintro ⟨y,rfl⟩
    obtain ⟨i,hi⟩ := point_has_one p
    let u := (basisPoint i).val
    have hu : dot u p.val=1 := by rw [dot_basisPoint]; exact hi
    let B := outerMatrix (x+y) u
    have hB : matrixAt B p.val=x+y := by rw [matrixAt_outer,hu,one_smul]
    obtain ⟨g,hg⟩ := codeRowKernel_translation_lift B
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨g,?_⟩
    change g.val • coordinateCross (p,x)=coordinateCross (p,y)
    rw [coordinateCross_action,hg]
    change coordinateCross (p,x+matrixAt B p.val)=_
    rw [hB,←add_assoc,vector_add_self,zero_add]

 theorem codeRowKernel_coordinate_stabilizer_order (p : Point) (x : E) :
    Nat.card (MulAction.stabilizer codeRowKernel (coordinateCross (p,x)))=2048 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup codeRowKernel (coordinateCross (p,x)))
  rw [Nat.card_prod,codeRowKernel_coordinate_orbit,coordinateRowFrame_card,codeRowKernel_order] at h
  omega

noncomputable abbrev codeRowReferenceStabilizer := MulAction.stabilizer codeRowKernel localReferenceCross

theorem codeRowReferenceStabilizer_order : Nat.card codeRowReferenceStabilizer=2048 := by
  change Nat.card (MulAction.stabilizer codeRowKernel localReferenceCross)=2048
  rw [localReferenceCross_eq]
  exact codeRowKernel_coordinate_stabilizer_order _ _

end Atlas.Rudvalis
