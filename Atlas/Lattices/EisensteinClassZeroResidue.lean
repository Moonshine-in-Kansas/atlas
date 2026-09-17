import Atlas.Lattices.EisensteinFrameVectors

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra
attribute [local instance] Classical.propDecidable

/-- Actual coordinate residues are invariants of a theta-class. -/
theorem eisensteinClass_coordinateResidue (x y : EisensteinLattice)
    (h : eisensteinClass x=eisensteinClass y) (i : Fin 12) :
    eisensteinResidue (x.val i)=eisensteinResidue (y.val i) := by
  obtain ⟨w,hw⟩ := (Submodule.Quotient.eq _).mp h
  have he := congrArg (fun z : EisensteinLattice => eisensteinResidue (z.val i)) hw
  change eisensteinResidue (eisensteinTheta*w.val i)=eisensteinResidue (x.val i-y.val i) at he
  simp only [map_mul,map_sub,show eisensteinResidue eisensteinTheta=0 by decide +kernel,zero_mul] at he
  exact sub_eq_zero.mp he.symm

def eisensteinZeroResidue (x : EisensteinLattice) : Prop :=
  ∀ i,eisensteinResidue (x.val i)=0

theorem eisensteinZeroResidue_neg (x : EisensteinLattice) :
    eisensteinZeroResidue (-x) ↔ eisensteinZeroResidue x := by
  simp [eisensteinZeroResidue]

theorem eisensteinZeroResidue_class (x y : EisensteinLattice)
    (h : eisensteinClass x=eisensteinClass y) :
    eisensteinZeroResidue x ↔ eisensteinZeroResidue y := by
  simp only [eisensteinZeroResidue,eisensteinClass_coordinateResidue x y h]

/-- Zero scalar residue is intrinsic to a frame, independently of the chosen short vector. -/
theorem eisensteinZeroResidue_frame (F : EisensteinFrame) (x y : EisensteinShell 6)
    (hx : x ∈ eisensteinFrameVectors F) (hy : y ∈ eisensteinFrameVectors F) :
    eisensteinZeroResidue x.val ↔ eisensteinZeroResidue y.val := by
  obtain ⟨c,hc,hF⟩ := eisensteinFrame_pair F
  have hxc := (Finset.mem_filter.mp hx).2
  have hyc := (Finset.mem_filter.mp hy).2
  rw [hF] at hxc hyc
  simp only [eisensteinFramePair,Finset.mem_insert,Finset.mem_singleton] at hxc hyc
  have he : eisensteinClass x.val=eisensteinClass y.val ∨
      eisensteinClass x.val= -eisensteinClass y.val := by
    rcases hxc with hx|hx <;> rcases hyc with hy|hy <;> rw [hx,hy] <;> simp
  rcases he with he|he
  · exact eisensteinZeroResidue_class _ _ he
  · rw [← map_neg] at he
    exact (eisensteinZeroResidue_class _ _ he).trans (eisensteinZeroResidue_neg y.val)

end Atlas.Lattices
