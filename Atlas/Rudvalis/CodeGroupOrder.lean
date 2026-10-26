import Atlas.Rudvalis.CodeTranslationImage
import Atlas.Rudvalis.CodeGroupKernel
import Atlas.Rudvalis.TwoRowObstruction

/-! Exact order of the full signed stabilizer, from its actual projection. -/
namespace Atlas.Rudvalis

theorem codePermutationHom_contains_translations :
    binaryTranslationSubgroup≤codePermutationHom.range := by
  apply binaryTranslationSubgroup_le_of_nine
  intro i
  exact ⟨nineCodeGenerator i,nineCodeGenerator_projection i⟩

theorem codePermutationHom_surjective : Function.Surjective codePermutationHom := by
  have hk : binaryBlockLinearHom.ker≤codePermutationHom.range := by
    rw [binaryBlockLinearHom_kernel_translations]
    exact codePermutationHom_contains_translations
  have hm : codePermutationHom.range.map binaryBlockLinearHom=⊤ := by
    rw [← MonoidHom.range_comp]
    exact MonoidHom.range_eq_top.mpr codeBlockLinearHom_surjective
  apply MonoidHom.range_eq_top.mp
  have he := Subgroup.comap_map_eq_self hk
  rw [hm,Subgroup.comap_top] at he
  exact he.symm

theorem codeGroup_order : Nat.card codeGroup=1376256 := by
  rw [codeGroup_order_of_surjective codePermutationHom_surjective,binaryPermutationGroup_order]

/-- The full kernel of the induced action on the seven Fano blocks. -/
noncomputable abbrev codeRowKernel := codeBlockLinearHom.ker

theorem codeRowKernel_order : Nat.card codeRowKernel=8192 := by
  have h := codeBlockLinearHom.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr codeBlockLinearHom_surjective,
    Subgroup.card_top,binaryLinearGroup_order,codeGroup_order] at h
  change Nat.card codeBlockLinearHom.ker=8192
  omega

theorem quaternary_minimum_not_two_rows (p q : Point) (hpq : p≠q)
    (w : QuaternaryWord) (hw : w∈quaternaryCode)
    (hweight : Atlas.Codes.Quaternary.euclideanWeight w=16) :
    Atlas.Codes.Quaternary.reduce w≠rowWord p+rowWord q :=
  quaternary_minimum_not_two_rows_of_surjective codePermutationHom_surjective p q hpq w hw hweight

end Atlas.Rudvalis
