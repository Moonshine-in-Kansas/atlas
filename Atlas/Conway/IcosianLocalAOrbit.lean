import Atlas.Conway.IcosianLocalCOrbit
import Atlas.Conway.IcosianAxisRootGeometry

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes

def icosianPureBlockPermutation (p : Equiv.Perm (Fin 3)) : icosianLiftedMonomial :=
  ⟨⟨1,p⟩,by
    change icosianMonomialReduction ⟨1,p⟩∈icosianGlueMonomialStabilizer GoldenFour
    rw [icosianGlueMonomialStabilizer_iff]
    change icosianUnitBlockReduction 1∈icosianGlueBlockStabilizer GoldenFour
    rw [map_one]
    exact (icosianGlueBlockStabilizer GoldenFour).one_mem⟩

theorem icosianPureBlockPermutation_axis (p : Equiv.Perm (Fin 3)) (i : Fin 3) :
    icosianMonomialToHermitian (icosianPureBlockPermutation p) • icosianRootAxisPoint i=
      icosianRootAxisPoint (p i) := by
  apply Subtype.ext
  change icosianMonomialToHermitian (icosianPureBlockPermutation p) •
    (icosianRootAxisPoint i).val=(icosianRootAxisPoint (p i)).val
  rw [icosianRootAxisPoint_val,icosianRootAxisPoint_val,icosianMonomial_axis]
  rfl

def icosianAxisShapeParameter (i : Fin 3) : IcosianRootPointShape 0 :=
  ⟨icosianRootAxisPoint i,icosianAxisRoot (i,1),rfl,
    (icosianRootShape_axis _).mpr (icosianAxisRoot_axis (i,1))⟩

theorem icosianAxisShapeParameter_injective : Function.Injective icosianAxisShapeParameter := by
  intro i j h
  exact icosianRootAxisPoint_injective (congrArg (fun p : IcosianRootPointShape 0 => p.val) h)

theorem icosianAxisShapeParameter_surjective : Function.Surjective icosianAxisShapeParameter :=
  ((Nat.bijective_iff_injective_and_card icosianAxisShapeParameter).mpr
    ⟨icosianAxisShapeParameter_injective,by rw [icosianRootPointShape_card]; norm_num⟩).2

theorem icosianLocalA_full_frame_orbit (p : IcosianRootPoint) :
    HasIcosianRootPointShape p 0 ↔
      ∃ g : icosianCoordinateFrameStabilizer,g.val • icosianRootAxisPoint 0=p := by
  constructor
  · intro hp
    obtain ⟨i,hi⟩ := icosianAxisShapeParameter_surjective ⟨p,hp⟩
    let m := icosianPureBlockPermutation (Equiv.swap 0 i)
    refine ⟨⟨icosianMonomialToHermitian m,icosianMonomial_mem_frameStabilizer m⟩,?_⟩
    have he : icosianRootAxisPoint i=p := congrArg Subtype.val hi
    rw [← he]
    simpa [m] using icosianPureBlockPermutation_axis (Equiv.swap 0 i) 0
  · rintro ⟨g,rfl⟩
    exact (icosianCoordinateFrame_rootPoint_shape g (icosianRootAxisPoint 0) 0).mpr
      (icosianAxisShapeParameter 0).property

theorem icosianLocalA_full_frame_stabilizer_card :
    Nat.card (MulAction.stabilizer icosianCoordinateFrameStabilizer (icosianRootAxisPoint 0))=768 := by
  have heq : MulAction.orbit icosianCoordinateFrameStabilizer (icosianRootAxisPoint 0)=
      {p : IcosianRootPoint | HasIcosianRootPointShape p 0} := by
    ext p
    exact (icosianLocalA_full_frame_orbit p).symm
  have ho : Nat.card (MulAction.orbit icosianCoordinateFrameStabilizer (icosianRootAxisPoint 0))=3 := by
    rw [Nat.card_congr (Equiv.setCongr heq)]
    exact icosianRootPointShape_card 0
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    icosianCoordinateFrameStabilizer (icosianRootAxisPoint 0))
  rw [Nat.card_prod,ho,icosianCoordinateFrameStabilizer_card] at h
  omega

end Atlas.Conway
