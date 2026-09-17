import Atlas.Fischer.OctadFusionCounts
import Atlas.Fischer.OctadicFrameConjugation
import Atlas.Fischer.DuadFibreChoiceIndependence
import Atlas.Fischer.ResidueModels

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- A concrete octad witnessing the local fusion, obtained from the proved
168/42/6 counts in the actual Golay design. -/
theorem octad_fusion_exists (F : Octad) (S : Finset Omega) (hSF : S ⊆ F.val)
    (hS : S.card≤2) (x : Omega) (hx : x∉F.val) :
    ∃ O : Octad,insert x S ⊆ O.val ∧ (O.val∩F.val).card=2 := by
  classical
  have hc := octad_fusion_count F S hSF hS x hx
  have hp : 0<octadIntersectionCount F.val (insert x S) 2 := by
    rw [hc]
    split_ifs <;> norm_num
  obtain ⟨O,hO⟩ := Finset.card_pos.mp hp
  obtain ⟨hO,hmark,hcard⟩ := Finset.mem_filter.mp hO
  exact ⟨⟨O,hO⟩,hmark,hcard⟩

/-- An actual octadic root involution fixing S and x fuses an octadic point
with a duadic point, on the original distinguished class. -/
theorem octadic_residue_fusion (S : Finset Omega) (hS : S.card≤2)
    (x : Omega) (F : Octad) (hSF : S ⊆ F.val) (hxF : x∉F.val)
    (χ : OctadicCharacter F) :
    ∃ p : RootDuad, S ⊆ p.val ∧ x∉p.val ∧
      ∃ ξ : Module.Dual Bit (duadShortenedCode p.val),
        ∃ g : residueCentralizer (insert x S),
          (MulAut.conj g.val) (distinguishedRootElement (.inr (.inl ⟨F,χ⟩)))=
            distinguishedRootElement (.inr (.inr ⟨p,ξ⟩)) := by
  classical
  obtain ⟨O,hSO,hOF⟩ := octad_fusion_exists F S hSF hS x hxF
  let p : RootDuad := ⟨O.val∩F.val,hOF⟩
  let Q := chosenOctadCalibration O
  let R := chosenOctadCalibration F
  obtain ⟨ξ,hξ⟩ := duadCharacterProduct_is_chosen p.val p.prop O F rfl Q R
    (duadCharacterEquiv p.val p.prop O F rfl (0,χ))
  rw [duadCharacterProduct_equiv] at hξ
  have hv : rootMap (octadicRoot Q 0) (octadicRoot R χ)=chosenDuadicRoot p ξ := by
    have he := duadOctadicProduct_eq_reflection hOF Q R 0 χ
    rw [octadicReflection_apply] at he
    exact he.symm.trans hξ
  let g : residueCentralizer (insert x S) := ⟨distinguishedRootElement (.inr (.inl ⟨O,0⟩)),by
    apply (mem_markedPentadPointwise_iff _ _).mpr
    intro i hi
    exact octadicRoot_conjugation_inside O 0 i (hSO hi)⟩
  refine ⟨p,?_,?_,ξ,g,?_⟩
  · exact Finset.subset_inter (fun i hi => hSO (Finset.mem_insert_of_mem hi)) hSF
  · exact fun h => hxF (Finset.mem_inter.mp h).2
  · apply distinguishedRootElement_conjugation
    apply Subtype.ext
    change (displayedRootRayInvolution (.inr (.inl ⟨O,0⟩))
      (displayedRayOfParameter (.inr (.inl ⟨F,χ⟩)))).val=_
    rw [displayedRootRayInvolution_parameter_value]
    change rootRay (rootMap (octadicRoot Q 0) (octadicRoot R χ))=_
    rw [hv]
    rfl

end Atlas.Fischer
