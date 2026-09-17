import Atlas.Conway.EisensteinConstantNineFrameSign
import Atlas.Lattices.EisensteinConstantClassPartition

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

/-- The intrinsic correction sign of an actual constant-hexad norm-nine frame. -/
def EisensteinNineSignFrame (b : ZMod 3) (F : EisensteinFrame) : Prop :=
  ∃ s : Finset (Fin 12),s ∈ ternaryConstantHexads ∧ ∃ k : Fin 12,k ∉ s ∧
    ∃ z : ZMod 3,∃ t : TernaryWord,(∑ i ∈ s,t i)=b ∧ ∃ x : EisensteinShell 6,
      x.val.val=eisensteinTheta • eisensteinConstantNineForm s k b z t ∧ eisensteinFrameOfVector x=F

theorem eisensteinConstantNineForm_wordResidue (s : Finset (Fin 12)) (k : Fin 12)
    (b z : ZMod 3) (t : TernaryWord) :
    eisensteinWordResidue (eisensteinConstantNineForm s k b z t)=ternaryTriadWord s := by
  funext i
  exact eisensteinConstantNineForm_residue s k b z t i

/-- The correction sign is well defined on the actual intrinsic frame, independent of
its vector, support, orientation, and coordinate phases. -/
theorem eisensteinNineSignFrame_unique (b d : ZMod 3) (F : EisensteinFrame)
    (hb : EisensteinNineSignFrame b F) (hd : EisensteinNineSignFrame d F) : b=d := by
  obtain ⟨s,hs,k,hk,z,t,ht,x,hx,hF⟩ := hb
  obtain ⟨r,hr,l,hl,w,v,hv,y,hy,hG⟩ := hd
  have hp : eisensteinFramePair (eisensteinClass x.val)=eisensteinFramePair (eisensteinClass y.val) :=
    congrArg Subtype.val (hF.trans hG.symm)
  have hpart := eisenstein_constant_frame_partition s r x y _ _ hx hy
    (eisensteinConstantNineForm_wordResidue s k b z t)
    (eisensteinConstantNineForm_wordResidue r l d w v) hp
  have hU : eisensteinTheta • eisensteinConstantNineForm s k b z t ∈ eisensteinLeechModule :=
    hx ▸ x.val.property
  have hV : eisensteinTheta • eisensteinConstantNineForm r l d w v ∈ eisensteinLeechModule :=
    hy ▸ y.val.property
  have he : eisensteinFramePair (eisensteinClass ⟨_,hU⟩)=eisensteinFramePair (eisensteinClass ⟨_,hV⟩) := by
    have hxx : (⟨_,hU⟩ : EisensteinLattice)=x.val := Subtype.ext hx.symm
    have hyy : (⟨_,hV⟩ : EisensteinLattice)=y.val := Subtype.ext hy.symm
    rw [hxx,hyy]
    exact hp
  rcases (ternaryConstantHexadPair_eq_iff s r).mp hpart with h|h
  · subst r
    exact eisensteinConstantNine_frame_sign_same s hs k l hk hl b d z w t v ht hv hU hV he
  · have hrc : r=sᶜ := by rw [h,compl_compl]
    subst r
    have hls : l ∈ s := by simpa using hl
    exact eisensteinConstantNine_frame_sign_compl s hs k l hk hls b d z w t v ht hU hV he

end Atlas.Conway
