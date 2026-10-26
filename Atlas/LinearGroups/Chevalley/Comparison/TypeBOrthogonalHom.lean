import Atlas.LinearAlgebra.ConjugationRestriction
import Atlas.LinearGroups.Chevalley.Comparison.TypeBSpinProjection
import Atlas.LinearGroups.Chevalley.Comparison.TypeBSpinSiegelCoordinates
import Atlas.LinearGroups.Chevalley.WeightCompanionLeftInduction

/-! The actual selected spin block induces a marked odd quadratic action.
The lift is unique through vector-injective gamma, including characteristic two.
No faithfulness of the Clifford algebra, source order or simplicity is used. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeB
open Classical ClassicalData Integral.Minuscule Atlas.BooleanSpin
open Atlas.LinearAlgebra Atlas.Orthogonal
variable (n : ℕ) (hn : 2 ≤ n+1) (F : Type*) [Field F]

private abbrev Compatible (g : SelectedWeightCompanion (.B (n+1) hn) F)
    (h : O_B (n+1) F) : Prop :=
  ConjugationCompatible (spinMatrixHom n hn F) (spinMatrixGamma n F)
    (isometrySubgroup (formB (n+1) F)) g h

private theorem compatible_X_long (i : Fin n) (t : F) :
    Compatible n hn F (selectedWeightCompanionX (.B (n+1) hn) F i.castSucc t)
      (oddLong (n+1) F i.castSucc i.succ (ne_of_lt i.castSucc_lt_succ) t) := by
  intro v
  rw [spinMatrixHom_X, spinMatrixHom_inv_X]
  change _ = matrix F (spinGamma (n+1) F
    ((oddLong (n+1) F i.castSucc i.succ (ne_of_lt i.castSucc_lt_succ) t).val v))
  rw [← longCoordinates_eq_oddLong]
  exact spin_X_simple_long_gamma n F i t v

private theorem compatible_Y_long (i : Fin n) (t : F) :
    Compatible n hn F (selectedWeightCompanionY (.B (n+1) hn) F i.castSucc t)
      (oddLong (n+1) F i.succ i.castSucc (Ne.symm (ne_of_lt i.castSucc_lt_succ)) t) := by
  intro v
  rw [spinMatrixHom_Y, spinMatrixHom_inv_Y]
  change _ = matrix F (spinGamma (n+1) F
    ((oddLong (n+1) F i.succ i.castSucc (Ne.symm (ne_of_lt i.castSucc_lt_succ)) t).val v))
  rw [← longCoordinates_eq_oddLong]
  exact spin_Y_simple_long_gamma n F i t v

private theorem compatible_X_short (t : F) :
    Compatible n hn F (selectedWeightCompanionX (.B (n+1) hn) F (Fin.last n) t)
      (oddShortUpper (n+1) F (Fin.last n) t) := by
  intro v
  rw [spinMatrixHom_X, spinMatrixHom_inv_X]
  change _ = matrix F (spinGamma (n+1) F ((oddShortUpper (n+1) F (Fin.last n) t).val v))
  rw [← shortUpperCoordinates_eq_oddShortUpper]
  exact spin_X_simple_short_gamma n F t v

private theorem compatible_Y_short (t : F) :
    Compatible n hn F (selectedWeightCompanionY (.B (n+1) hn) F (Fin.last n) t)
      (oddShortLower (n+1) F (Fin.last n) t) := by
  intro v
  rw [spinMatrixHom_Y, spinMatrixHom_inv_Y]
  change _ = matrix F (spinGamma (n+1) F ((oddShortLower (n+1) F (Fin.last n) t).val v))
  rw [← shortLowerCoordinates_eq_oddShortLower]
  exact spin_Y_simple_short_gamma n F t v

private theorem compatible_X (i : Fin (n+1)) (t : F) :
    ∃ h : O_B (n+1) F, Compatible n hn F
      (selectedWeightCompanionX (.B (n+1) hn) F i t) h := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · exact ⟨_, compatible_X_short n hn F t⟩
  · exact ⟨_, compatible_X_long n hn F k t⟩

private theorem compatible_Y (i : Fin (n+1)) (t : F) :
    ∃ h : O_B (n+1) F, Compatible n hn F
      (selectedWeightCompanionY (.B (n+1) hn) F i t) h := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · exact ⟨_, compatible_Y_short n hn F t⟩
  · exact ⟨_, compatible_Y_long n hn F k t⟩

/-- Every actual selected companion element has a genuine quadratic-isometry
lift of its spin-block conjugation. This follows from the actual generators. -/
theorem spinMatrix_conjugation_lift (g : SelectedWeightCompanion (.B (n+1) hn) F) :
    ∃ h : O_B (n+1) F,
      ConjugationCompatible (spinMatrixHom n hn F) (spinMatrixGamma n F)
        (isometrySubgroup (formB (n+1) F)) g h := by
  apply weightCompanion_induction_left (rootDatum (.B (n+1) hn)).pairing
    (rootDatum (.B (n+1) hn)).base (selectedWeightOrbits (.B (n+1) hn))
    (selectedWeightOrbits_closed (.B (n+1) hn))
    (selectedWeightOrbits_minuscule (.B (n+1) hn)) F ?_ ?_ ?_ g
  · exact ⟨1, conjugationCompatible_one _ _ _⟩
  · intro j t h hh
    obtain ⟨i,rfl⟩ := (rootDatum (.B (n+1) hn)).indexEquiv.surjective j
    change Fin (n+1) at i
    change ∃ a : O_B (n+1) F, Compatible n hn F
      (selectedWeightCompanionX (.B (n+1) hn) F i t * h) a
    obtain ⟨a,ha⟩ := compatible_X n hn F i t
    obtain ⟨k,hk⟩ := hh
    exact ⟨a*k, conjugationCompatible_mul _ _ _ ha hk⟩
  · intro j t h hh
    obtain ⟨i,rfl⟩ := (rootDatum (.B (n+1) hn)).indexEquiv.surjective j
    change Fin (n+1) at i
    change ∃ a : O_B (n+1) F, Compatible n hn F
      (selectedWeightCompanionY (.B (n+1) hn) F i t * h) a
    obtain ⟨a,ha⟩ := compatible_Y n hn F i t
    obtain ⟨k,hk⟩ := hh
    exact ⟨a*k, conjugationCompatible_mul _ _ _ ha hk⟩

/-- The concrete homomorphism from the primary selected B companion to the
existing odd quadratic isometry group, defined by its unique gamma action. -/
def orthogonalHom : SelectedWeightCompanion (.B (n+1) hn) F →* O_B (n+1) F :=
  conjugationRestrictionHom (spinMatrixHom n hn F) (spinMatrixGamma n F)
    (isometrySubgroup (formB (n+1) F)) (spinMatrixGamma_injective n F)
    (spinMatrix_conjugation_lift n hn F)

theorem orthogonalHom_gamma (g : SelectedWeightCompanion (.B (n+1) hn) F)
    (v : VectorB (n+1) F) :
    spinMatrixHom n hn F g * spinMatrixGamma n F v * spinMatrixHom n hn F g⁻¹ =
      spinMatrixGamma n F ((orthogonalHom n hn F g).val v) :=
  conjugationRestrictionHom_compatible _ _ _ _ _ g v

theorem orthogonalHom_X_long (i : Fin n) (t : F) :
    orthogonalHom n hn F (selectedWeightCompanionX (.B (n+1) hn) F i.castSucc t) =
      oddLong (n+1) F i.castSucc i.succ (ne_of_lt i.castSucc_lt_succ) t :=
  conjugationRestrictionHom_eq _ _ _ _ _ _ _ (compatible_X_long n hn F i t)

theorem orthogonalHom_Y_long (i : Fin n) (t : F) :
    orthogonalHom n hn F (selectedWeightCompanionY (.B (n+1) hn) F i.castSucc t) =
      oddLong (n+1) F i.succ i.castSucc (Ne.symm (ne_of_lt i.castSucc_lt_succ)) t :=
  conjugationRestrictionHom_eq _ _ _ _ _ _ _ (compatible_Y_long n hn F i t)

theorem orthogonalHom_X_short (t : F) :
    orthogonalHom n hn F (selectedWeightCompanionX (.B (n+1) hn) F (Fin.last n) t) =
      oddShortUpper (n+1) F (Fin.last n) t :=
  conjugationRestrictionHom_eq _ _ _ _ _ _ _ (compatible_X_short n hn F t)

theorem orthogonalHom_Y_short (t : F) :
    orthogonalHom n hn F (selectedWeightCompanionY (.B (n+1) hn) F (Fin.last n) t) =
      oddShortLower (n+1) F (Fin.last n) t :=
  conjugationRestrictionHom_eq _ _ _ _ _ _ _ (compatible_Y_short n hn F t)

/-- In characteristic two the radical is fixed pointwise because gamma maps
it to scalar operators. No polar-form nondegeneracy is asserted. -/
theorem orthogonalHom_radical_charTwo (h2 : (2 : F)=0)
    (g : SelectedWeightCompanion (.B (n+1) hn) F) (z : F) :
    (orthogonalHom n hn F g).val (0,z) = (0,z) := by
  apply spinMatrixGamma_injective n F
  rw [← orthogonalHom_gamma]
  change spinMatrixHom n hn F g * matrix F (spinGamma (n+1) F (0,z)) *
    spinMatrixHom n hn F g⁻¹ = matrix F (spinGamma (n+1) F (0,z))
  simp only [spinGamma_radical_charTwo (n+1) F h2, map_smul, map_one]
  rw [mul_smul_comm, mul_one, smul_mul_assoc, ← map_mul, mul_inv_cancel, map_one]

theorem orthogonalHom_mem_elementary (g : SelectedWeightCompanion (.B (n+1) hn) F) :
    orthogonalHom n hn F g ∈ elementarySubgroup (formB (n+1) F) := by
  apply weightCompanion_induction_left (rootDatum (.B (n+1) hn)).pairing
    (rootDatum (.B (n+1) hn)).base (selectedWeightOrbits (.B (n+1) hn))
    (selectedWeightOrbits_closed (.B (n+1) hn))
    (selectedWeightOrbits_minuscule (.B (n+1) hn)) F ?_ ?_ ?_ g
  · rw [map_one]
    exact (elementarySubgroup _).one_mem
  · intro j t h hh
    obtain ⟨i,rfl⟩ := (rootDatum (.B (n+1) hn)).indexEquiv.surjective j
    change Fin (n+1) at i
    change orthogonalHom n hn F
      (selectedWeightCompanionX (.B (n+1) hn) F i t * h) ∈ _
    rw [map_mul]
    apply (elementarySubgroup _).mul_mem ?_ hh
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [orthogonalHom_X_short]
      exact oddShortUpper_mem_elementary _ _ _ _
    · rw [orthogonalHom_X_long]
      exact oddLong_mem_elementary _ _ _ _ _ _
  · intro j t h hh
    obtain ⟨i,rfl⟩ := (rootDatum (.B (n+1) hn)).indexEquiv.surjective j
    change Fin (n+1) at i
    change orthogonalHom n hn F
      (selectedWeightCompanionY (.B (n+1) hn) F i t * h) ∈ _
    rw [map_mul]
    apply (elementarySubgroup _).mul_mem ?_ hh
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [orthogonalHom_Y_short]
      exact oddShortLower_mem_elementary _ _ _ _
    · rw [orthogonalHom_Y_long]
      exact oddLong_mem_elementary _ _ _ _ _ _

def elementaryHom : SelectedWeightCompanion (.B (n+1) hn) F →*
    elementarySubgroup (formB (n+1) F) :=
  (orthogonalHom n hn F).codRestrict _ (orthogonalHom_mem_elementary n hn F)

end Atlas.Chevalley.Comparison.TypeB
