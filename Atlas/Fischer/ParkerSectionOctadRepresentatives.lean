import Atlas.Fischer.ParkerSectionOctadSigns

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- A hypothetical section transports a signed octad independently of the
Mathieu element realizing the prescribed octad transport. -/
theorem parkerSection_octad_transport_unique
    (s : Mathieu24CodeModel →* ParkerStandardGroup)
    (hs : parkerStandardProjection.comp s = MonoidHom.id _)
    (O P : Octad) (g h : Mathieu24CodeModel) (hg : g • O = P) (hh : h • O = P)
    (o : ParkerLoop) (ho : o.1 = octadWord O) : (s g).val o = (s h).val o := by
  have hk : (h⁻¹*g) • O = O := by rw [mul_smul, hg, ← hh, inv_smul_smul]
  have hf := parkerSection_fixes_octad s hs O (h⁻¹*g) hk o ho
  have he : s g = s h * s (h⁻¹*g) := by rw [← map_mul, mul_inv_cancel_left]
  rw [he]
  change (s h).val ((s (h⁻¹*g)).val o) = (s h).val o
  rw [hf]

/-- A hypothetical M24 complement supplies an equivariant choice of an
actual signed loop element above each octad. -/
theorem parkerSection_equivariant_octad_representatives
    (s : Mathieu24CodeModel →* ParkerStandardGroup)
    (hs : parkerStandardProjection.comp s = MonoidHom.id _)
    (O₀ : Octad) :
    ∃ q : Octad → ParkerLoop,
      (∀ O, (q O).1 = octadWord O) ∧
      (∀ g : Mathieu24CodeModel, ∀ O, q (g • O) = (s g).val (q O)) := by
  classical
  choose t ht using (fun O : Octad => MulAction.exists_smul_eq Mathieu24CodeModel O₀ O)
  let o : ParkerLoop := (octadWord O₀,0)
  let q : Octad → ParkerLoop := fun O => (s (t O)).val o
  refine ⟨q,?_,?_⟩
  · intro O
    change ((s (t O)).val o).1 = octadWord O
    rw [parkerStandardProjection_spec]
    have hp : parkerStandardProjection (s (t O)) = t O := DFunLike.congr_fun hs (t O)
    rw [hp]
    change parkerCodeEquiv (t O) (octadWord O₀) = octadWord O
    rw [← cubicTriangle_word_smul, ht]
  · intro g O
    have he := parkerSection_octad_transport_unique s hs O₀ (g • O)
      (t (g • O)) (g*t O) (ht _) (by rw [mul_smul, ht]) o rfl
    change (s (t (g • O))).val o = (s g).val ((s (t O)).val o)
    rw [he, map_mul]
    rfl

end Atlas.Fischer
