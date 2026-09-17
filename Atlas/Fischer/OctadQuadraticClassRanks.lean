import Atlas.Fischer.OctadQuadraticRanks

namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

/-- Rank is attached to an actual quadratic-function class: affine changes
preserve its normalized polar map. -/
noncomputable def binaryQuadraticClassPolarRank : BinaryQuadraticClasses → ℕ :=
  Quotient.lift (s := Submodule.quotientRel binaryAffineInQuadratic) (fun w : binaryQuadraticCode => binaryWalshPolarRank (binaryQuadraticWordForm w))
    (by
      intro w z h
      have h := (Submodule.quotientRel_def (p := binaryAffineInQuadratic)).mp h
      change w.val-z.val ∈ binaryAffineCode at h
      have hn : -z.val=z.val := by funext v; exact CharTwo.neg_eq _
      rw [sub_eq_add_neg,hn] at h
      unfold binaryWalshPolarRank
      rw [binaryQuadraticWordForm_polar_eq_of_affine w z h])

@[simp] theorem binaryQuadraticClassPolarRank_mk (w : binaryQuadraticCode) :
    binaryQuadraticClassPolarRank (Submodule.Quotient.mk w)=
      binaryWalshPolarRank (binaryQuadraticWordForm w) := rfl

theorem binaryQuadraticClassPolarRank_zero : binaryQuadraticClassPolarRank 0=0 := by
  have hq : binaryQuadraticWordForm (0 : binaryQuadraticCode)=0 := by
    apply QuadraticMap.ext
    intro v
    simp [binaryQuadraticWordForm_apply]
  change binaryWalshPolarRank (binaryQuadraticWordForm (0 : binaryQuadraticCode))=0
  rw [hq]
  have hp : (0 : QuadraticMap Bit BinaryFour Bit).polarBilin=0 := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    simp [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
  simp [binaryWalshPolarRank,hp]

noncomputable def octadClassPolarRank (O : Octad) (x : OctadEvenClasses O) : ℕ :=
  binaryQuadraticClassPolarRank (octadEvenQuadraticClassesEquiv O x)

@[simp] theorem octadClassPolarRank_zero (O : Octad) : octadClassPolarRank O 0=0 := by
  simp [octadClassPolarRank,binaryQuadraticClassPolarRank_zero]

/-- The rank-four assertion is a statement on the actual quotient class. -/
theorem octadClassPolarRank_duad (O : Octad) (c : golay)
    (h : (support c.val ∩ O.val).card=2) : octadClassPolarRank O (octadEvenClassMap O c)=4 := by
  rw [octadClassPolarRank,octadEvenQuadraticClassesEquiv_apply]
  exact octadQuadraticWord_rank_duad O c h

/-- Complementary tetrads represent the same rank-two quotient class. -/
theorem octadClassPolarRank_tetrad (O : Octad) (c : golay)
    (h : (support c.val ∩ O.val).card=4) : octadClassPolarRank O (octadEvenClassMap O c)=2 := by
  rw [octadClassPolarRank,octadEvenQuadraticClassesEquiv_apply]
  exact octadQuadraticWord_rank_tetrad O c h

theorem octadClassQuadratic_duad (O : Octad) (c : golay)
    (h : (support c.val ∩ O.val).card=2) : octadClassQuadratic O (octadEvenClassMap O c)=1 := by
  change ((hammingNorm (octadEvenRestriction O c).val/2 : ℕ) : Bit)=1
  rw [octadEvenRestriction_weight,h]
  rfl

theorem octadClassQuadratic_tetrad (O : Octad) (c : golay)
    (h : (support c.val ∩ O.val).card=4) : octadClassQuadratic O (octadEvenClassMap O c)=0 := by
  change ((hammingNorm (octadEvenRestriction O c).val/2 : ℕ) : Bit)=0
  rw [octadEvenRestriction_weight,h]
  rfl

end Atlas.Fischer
