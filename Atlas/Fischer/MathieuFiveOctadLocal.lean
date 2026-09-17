import Atlas.Fischer.MathieuOctadMarkedLocal

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem mathieuFiveFixer_stabilizes_octad (O : Octad) (P : Finset Omega)
    (hPO : P ⊆ O.val) (hP : P.card=5)
    (g : fixingSubgroup Mathieu24CodeModel (P : Set Omega)) :
    g.val ∈ mathieuOctadStabilizer O := by
  rw [mathieuOctadStabilizer_iff]
  apply octad_unique_on_five P _ O.val hP
    (codePreserving_octad_forward g.val.val g.val.prop O.val O.prop) O.prop
  · intro i hi
    exact Finset.mem_image.mpr ⟨i,hPO hi,g.prop ⟨i,hi⟩⟩
  · exact hPO

def mathieuFiveFixerLocalHom (O : Octad) (P : Finset Omega)
    (hPO : P ⊆ O.val) (hP : P.card=5) :
    fixingSubgroup Mathieu24CodeModel (P : Set Omega) →*
      mathieuOctadRestrictedLocal O (octadMarkedPoints O P) where
  toFun g := ⟨⟨g.val,mathieuFiveFixer_stabilizes_octad O P hPO hP g⟩,
    (mathieuOctadMarkedLocal_iff O P hPO _).mpr (fun i hi => g.prop ⟨i,hi⟩)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The quotient seen by an actual five-point fixer is precisely the alternating
permutation action on the three remaining octad coordinates. -/
def mathieuFiveFixerComplementHom (O : Octad) (P : Finset Omega)
    (hPO : P ⊆ O.val) (hP : P.card=5) :
    fixingSubgroup Mathieu24CodeModel (P : Set Omega) →*
      alternatingGroup (↑((octadMarkedPoints O P)ᶜ)) :=
  (mathieuOctadComplementHom O (octadMarkedPoints O P)).comp
    (mathieuFiveFixerLocalHom O P hPO hP)

theorem mathieuFiveFixerComplement_kernel (O : Octad) (S P : Finset Omega)
    (hSO : S ⊆ O.val) (hPO : P ⊆ O.val) (hP : P.card=5)
    (g : fixingSubgroup Mathieu24CodeModel (P : Set Omega))
    (hg : mathieuFiveFixerComplementHom O P hPO hP g=1) :
    g.val ∈ mathieuTranslationGenerated S := by
  have hk : mathieuFiveFixerLocalHom O P hPO hP g ∈
      (mathieuOctadComplementHom O (octadMarkedPoints O P)).ker := hg
  rw [mathieuOctadComplementHom_ker] at hk
  exact Subgroup.subset_closure ⟨O,hSO,
    ⟨(mathieuFiveFixerLocalHom O P hPO hP g).val,hk⟩,rfl⟩

end Atlas.Fischer
