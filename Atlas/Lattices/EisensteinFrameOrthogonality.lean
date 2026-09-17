import Atlas.Lattices.EisensteinFrameLines

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra

/-- The phase classification of one class descends to scalar lines. -/
theorem eisenstein_sameClass_line_or_orthogonal (x y : EisensteinShell 6)
    (hc : eisensteinClass x.val = eisensteinClass y.val) :
    eisensteinScalarLine x = eisensteinScalarLine y ∨
      eisensteinHermitian (eisensteinCoordinateEmbedding x.val.val)
        (eisensteinCoordinateEmbedding y.val.val) = 0 := by
  have h := eisenstein_six_sameClass_phases_or_orthogonal x.val y.val x.property y.property hc
  rcases h with h | h | h | h
  · exact Or.inl (congrArg eisensteinScalarLine (Subtype.ext h))
  · apply Or.inl
    apply (eisensteinScalarLine_eq_iff y x).mpr
    refine ⟨rationalOmega, ?_⟩
    have he := congrArg (fun z : EisensteinLattice => eisensteinCoordinateEmbedding z.val) h
    rw [eisensteinLatticeRotation_embedding] at he
    exact he
  · apply Or.inl
    apply (eisensteinScalarLine_eq_iff y x).mpr
    refine ⟨rationalOmega*rationalOmega, ?_⟩
    rw [mul_smul]
    have he := congrArg (fun z : EisensteinLattice => eisensteinCoordinateEmbedding z.val) h
    rw [eisensteinLatticeRotation_embedding, eisensteinLatticeRotation_embedding] at he
    exact he
  · exact Or.inr h

def eisensteinSixNeg (x : EisensteinShell 6) : EisensteinShell 6 :=
  ⟨-x.val, (eisensteinNorm_neg x.val).trans x.property⟩

theorem eisensteinScalarLine_neg (x : EisensteinShell 6) :
    eisensteinScalarLine (eisensteinSixNeg x) = eisensteinScalarLine x := by
  apply (eisensteinScalarLine_eq_iff x (eisensteinSixNeg x)).mpr
  refine ⟨-1, ?_⟩
  change eisensteinCoordinateEmbedding (-x.val.val) = _
  rw [map_neg, neg_one_smul]

/-- The phase-or-orthogonal classification also holds across the two opposite classes. -/
theorem eisenstein_oppositeClasses_line_or_orthogonal (x y : EisensteinShell 6)
    (hc : eisensteinClass x.val = eisensteinClass y.val ∨
      eisensteinClass x.val = -eisensteinClass y.val) :
    eisensteinScalarLine x = eisensteinScalarLine y ∨
      eisensteinHermitian (eisensteinCoordinateEmbedding x.val.val)
        (eisensteinCoordinateEmbedding y.val.val) = 0 := by
  rcases hc with hc | hc
  · exact eisenstein_sameClass_line_or_orthogonal x y hc
  · have hh : eisensteinClass x.val = eisensteinClass (eisensteinSixNeg y).val := by
      change eisensteinClass x.val = eisensteinClass (-y.val)
      rw [map_neg]
      exact hc
    rcases eisenstein_sameClass_line_or_orthogonal x (eisensteinSixNeg y) hh with h | h
    · exact Or.inl (h.trans (eisensteinScalarLine_neg y))
    · apply Or.inr
      change eisensteinHermitian (eisensteinCoordinateEmbedding x.val.val)
        (eisensteinCoordinateEmbedding (-y.val.val)) = 0 at h
      rw [map_neg] at h
      change eisensteinHermitianLinearRight (eisensteinCoordinateEmbedding x.val.val)
        (-eisensteinCoordinateEmbedding y.val.val) = 0 at h
      rw [map_neg] at h
      exact neg_eq_zero.mp h

/-- Distinct short-vector lines of an intrinsic frame have orthogonal generators. -/
theorem eisensteinFrameVectors_orthogonal (F : EisensteinFrame)
    (x y : EisensteinShell 6) (hx : x ∈ eisensteinFrameVectors F)
    (hy : y ∈ eisensteinFrameVectors F) (hne : eisensteinScalarLine x ≠ eisensteinScalarLine y) :
    eisensteinHermitian (eisensteinCoordinateEmbedding x.val.val)
      (eisensteinCoordinateEmbedding y.val.val) = 0 := by
  obtain ⟨c, hc, he⟩ := eisensteinFrame_pair F
  have hxc : eisensteinClass x.val = c ∨ eisensteinClass x.val = -c := by
    simpa [eisensteinFrameVectors, he, eisensteinFramePair] using hx
  have hyc : eisensteinClass y.val = c ∨ eisensteinClass y.val = -c := by
    simpa [eisensteinFrameVectors, he, eisensteinFramePair] using hy
  have hclasses : eisensteinClass x.val = eisensteinClass y.val ∨
      eisensteinClass x.val = -eisensteinClass y.val := by
    rcases hxc with hx | hx <;> rcases hyc with hy | hy <;> rw [hx, hy] <;> simp
  exact (eisenstein_oppositeClasses_line_or_orthogonal x y hclasses).resolve_left hne

/-- Orthogonality of nonzero generators extends to their entire scalar lines. -/
theorem eisenstein_spans_orthogonal (x y : EisensteinRationalCoordinates)
    (hxy : eisensteinHermitian x y = 0)
    (u : EisensteinRationalCoordinates) (hu : u ∈ Submodule.span EisensteinRational {x})
    (v : EisensteinRationalCoordinates) (hv : v ∈ Submodule.span EisensteinRational {y}) :
    eisensteinHermitian u v = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv
  have hya : eisensteinHermitian y (a • x) = 0 := by
    change eisensteinHermitianLinearRight y (a • x) = 0
    rw [map_smul]
    change a * eisensteinHermitian y x = 0
    rw [eisensteinHermitian_zero_symm hxy, mul_zero]
  have hay := eisensteinHermitian_zero_symm hya
  change eisensteinHermitianLinearRight (a • x) (b • y) = 0
  rw [map_smul]
  change b * eisensteinHermitian (a • x) y = 0
  rw [hay, mul_zero]

/-- The twelve actual one-dimensional scalar subspaces of an intrinsic frame
are pairwise Hermitian orthogonal. -/
theorem eisensteinFrameLines_orthogonal (F : EisensteinFrame)
    (L M : Submodule EisensteinRational EisensteinRationalCoordinates)
    (hL : L ∈ eisensteinFrameLines F) (hM : M ∈ eisensteinFrameLines F) (hne : L ≠ M) :
    ∀ u ∈ L, ∀ v ∈ M, eisensteinHermitian u v = 0 := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hL
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hM
  exact eisenstein_spans_orthogonal _ _ (eisensteinFrameVectors_orthogonal F x y hx hy hne)

end Atlas.Lattices
