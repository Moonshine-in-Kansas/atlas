import Atlas.Fischer.MathieuTranslationAlignment

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The retained translation kernel is exactly the actual pointwise octad fixer. -/
theorem octadPointwiseEmbedding_range (O : Octad) :
    (octadPointwiseEmbedding O).range = fixingSubgroup Mathieu24CodeModel (O.val : Set Omega) := by
  classical
  ext g
  constructor
  · rintro ⟨t,rfl⟩ i
    exact octadPointwiseEmbedding_fixes O t i.val i.prop
  · intro hg
    have hs : g ∈ mathieuOctadStabilizer O := by
      rw [mathieuOctadStabilizer_iff]
      change O.val.image g.val = O.val
      apply Finset.ext
      intro i
      constructor
      · intro hi
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
        have he : g.val j=j := hg ⟨j,hj⟩
        rwa [he]
      · intro hi
        exact Finset.mem_image.mpr ⟨i,hi,hg ⟨i,hi⟩⟩
    have hk : (⟨g,hs⟩ : MathieuOctadStabilizer O) ∈ mathieuOctadPointwise O := by
      change mathieuOctadAlternatingHom O ⟨g,hs⟩=1
      apply Subtype.ext
      apply Equiv.ext
      intro i
      apply Subtype.ext
      exact hg i
    exact ⟨⟨⟨g,hs⟩,hk⟩,rfl⟩

theorem octadTranslationGenerators_conj (S : Finset Omega)
    (g : fixingSubgroup Mathieu24CodeModel (S : Set Omega))
    (t : Mathieu24CodeModel) (ht : t ∈ octadTranslationGenerators S) :
    g.val*t*g.val⁻¹ ∈ octadTranslationGenerators S := by
  classical
  obtain ⟨O,hSO,u,rfl⟩ := ht
  have hSgO : S ⊆ (g.val • O).val := by
    intro i hi
    change i ∈ O.val.image g.val.val
    exact Finset.mem_image.mpr ⟨i,hSO hi,g.prop ⟨i,hi⟩⟩
  have hf : g.val*octadPointwiseEmbedding O u*g.val⁻¹ ∈
      fixingSubgroup Mathieu24CodeModel ((g.val • O).val : Set Omega) := by
    intro i
    obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp i.prop
    change g.val.val ((octadPointwiseEmbedding O u).val (g.val.val⁻¹ i.val))=i.val
    rw [← hji,Equiv.Perm.inv_def,Equiv.symm_apply_apply,
      octadPointwiseEmbedding_fixes O u j hj]
  rw [← octadPointwiseEmbedding_range] at hf
  obtain ⟨v,hv⟩ := hf
  exact ⟨g.val • O,hSgO,v,hv⟩

/-- The translation-generated subgroup is normal in the corresponding actual
Mathieu pointwise stabilizer. -/
def mathieuTranslationNormalSubgroup (S : Finset Omega) :
    Subgroup (fixingSubgroup Mathieu24CodeModel (S : Set Omega)) :=
  (mathieuTranslationGenerated S).comap
    (fixingSubgroup Mathieu24CodeModel (S : Set Omega)).subtype

instance mathieuTranslationNormalSubgroup_normal (S : Finset Omega) :
    (mathieuTranslationNormalSubgroup S).Normal := by
  constructor
  intro t ht g
  change g.val*t.val*g.val⁻¹ ∈ mathieuTranslationGenerated S
  change t.val ∈ Subgroup.closure (octadTranslationGenerators S) at ht
  have hc : ∀ x ∈ Subgroup.closure (octadTranslationGenerators S),
      g.val*x*g.val⁻¹ ∈ mathieuTranslationGenerated S := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (octadTranslationGenerators_conj S g x hx)
    | one => simpa using (mathieuTranslationGenerated S).one_mem
    | mul x y hx hy ihx ihy =>
        have h := (mathieuTranslationGenerated S).mul_mem ihx ihy
        simpa only [mul_assoc,inv_mul_cancel_left] using h
    | inv x hx ihx =>
        have h := (mathieuTranslationGenerated S).inv_mem ihx
        simpa only [mul_inv_rev,inv_inv,mul_assoc] using h
  exact hc t.val ht


end Atlas.Fischer
