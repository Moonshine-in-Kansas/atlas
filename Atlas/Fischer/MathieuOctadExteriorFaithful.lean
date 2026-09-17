import Atlas.Fischer.MathieuOctadStabilizer
import Atlas.Fischer.OctadRestrictionCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Fixing the six exterior points of a crossing octad fixes that whole octad. -/
theorem mathieuOctad_fix_crossing (O : Octad) (g : MathieuOctadStabilizer O)
    (hg : ∀ i, i ∉ O.val → g.val.val i = i)
    (B : Finset Omega) (hB : B ∈ octads) (hBO : (B ∩ O.val).card = 2) :
    permuteBlock g.val.val B = B := by
  classical
  have hc := Finset.card_sdiff_add_card_inter B O.val
  rw [octad_size B hB,hBO] at hc
  obtain ⟨F,hF,hFc⟩ := Finset.exists_subset_card_eq
    (s := B \ O.val) (n := 5) (by omega)
  apply octad_unique_on_five F _ B hFc
    (codePreserving_octad_forward g.val.val g.val.prop B hB) hB
  · intro i hi
    have hb := hF hi
    have hib := (Finset.mem_sdiff.mp hb).1
    have hio := (Finset.mem_sdiff.mp hb).2
    exact Finset.mem_image.mpr ⟨i,hib,hg i hio⟩
  · exact hF.trans Finset.sdiff_subset

theorem mathieuOctad_fix_duad (O : Octad) (g : MathieuOctadStabilizer O)
    (hg : ∀ i, i ∉ O.val → g.val.val i = i)
    (S : Finset Omega) (hSO : S ⊆ O.val) (hS : S.card = 2) :
    permuteBlock g.val.val S = S := by
  classical
  have hn : 0 < octadRestrictionCount O.val S := by
    rw [octadRestrictionCount_duad O.val S O.prop hSO hS]; decide
  obtain ⟨B,hB⟩ := Finset.card_pos.mp hn
  obtain ⟨hB,hBS⟩ := Finset.mem_filter.mp hB
  have hf := mathieuOctad_fix_crossing O g hg B hB (by rw [hBS,hS])
  have ho := (mathieuOctadStabilizer_iff O g.val).mp g.prop
  rw [← hBS]
  change (B ∩ O.val).image g.val.val = B ∩ O.val
  rw [Finset.image_inter _ _ g.val.val.injective]
  exact congrArg₂ (fun A C : Finset Omega => A ∩ C) hf ho

/-- An element of the full octad stabilizer fixing its complement is identity. -/
theorem mathieuOctad_eq_one_of_exterior_fixed (O : Octad) (g : MathieuOctadStabilizer O)
    (hg : ∀ i, i ∉ O.val → g.val.val i = i) : g = 1 := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro i
  by_cases hi : i ∈ O.val
  · by_contra hgi
    have hj : ∃ j ∈ O.val, j ≠ i ∧ j ≠ g.val.val i := by
      by_contra! h
      have hs : O.val ⊆ {i,g.val.val i} := by
        intro j hj
        by_cases he : j=i
        · simp [he]
        · simp [h j hj he]
      have hc := Finset.card_le_card hs
      have hb : ({i,g.val.val i} : Finset Omega).card ≤ 2 := by
        calc
          _ ≤ ({g.val.val i} : Finset Omega).card + 1 := Finset.card_insert_le _ _
          _ = 2 := by simp
      rw [octad_size O.val O.prop] at hc
      omega
    obtain ⟨j,hj,hji,hjg⟩ := hj
    have hf := mathieuOctad_fix_duad O g hg {i,j}
      (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hi
          · exact Finset.mem_singleton.mp hx ▸ hj)
      (by simp [Ne.symm hji])
    have hm : g.val.val i ∈ ({i,j} : Finset Omega) := by
      rw [← hf]
      exact Finset.mem_image.mpr ⟨i,by simp,rfl⟩
    have hh : g.val.val i = i ∨ g.val.val i = j := by simpa using hm
    exact hh.elim hgi (fun h => hjg h.symm)
  · exact hg i hi

theorem mathieuOctadExteriorHom_injective (O : Octad) :
    Function.Injective (mathieuOctadExteriorHom O) := by
  intro g h he
  have hk : mathieuOctadExteriorHom O (g*h⁻¹) = 1 := by
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hid : g*h⁻¹=1 := by
    apply mathieuOctad_eq_one_of_exterior_fixed
    intro i hi
    exact congrArg (fun p : Equiv.Perm (OctadExterior O) => (p ⟨i,hi⟩).val) hk
  exact mul_inv_eq_one.mp hid

end Atlas.Fischer
