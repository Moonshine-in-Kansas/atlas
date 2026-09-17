import Atlas.LinearGroups.Orthogonal.BConstruction
import Atlas.LinearGroups.Orthogonal.ProjectiveFieldTransport
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Specified field transport for the actual public B family -/
noncomputable section
namespace Atlas.Orthogonal
variable {F K L : Type*} [Field F] [Field K] [Field L]

theorem fieldEquivElementaryB_refl (n : ℕ) (g : elementarySubgroup (formB n F)) :
    fieldEquivElementaryB (RingEquiv.refl F) g = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rfl

theorem fieldEquivElementaryB_trans (n : ℕ) (e : F ≃+* K) (f : K ≃+* L)
    (g : elementarySubgroup (formB n F)) :
    fieldEquivElementaryB (e.trans f) g = fieldEquivElementaryB f (fieldEquivElementaryB e g) := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rfl

theorem B_fieldEquiv_refl (n : ℕ) : B_fieldEquiv n (RingEquiv.refl F) = MulEquiv.refl _ := by
  ext g
  obtain ⟨a,rfl⟩ := projectiveElementaryMap_surjective _ g
  rw [B_fieldEquiv_projection, fieldEquivElementaryB_refl]
  rfl

theorem B_fieldEquiv_trans (n : ℕ) (e : F ≃+* K) (f : K ≃+* L) :
    B_fieldEquiv n (e.trans f) = (B_fieldEquiv n e).trans (B_fieldEquiv n f) := by
  ext g
  obtain ⟨a,rfl⟩ := projectiveElementaryMap_surjective _ g
  change B_fieldEquiv n (e.trans f) (projectiveElementaryMap _ a) =
    B_fieldEquiv n f (B_fieldEquiv n e (projectiveElementaryMap _ a))
  rw [B_fieldEquiv_projection, B_fieldEquiv_projection,
    B_fieldEquiv_projection, fieldEquivElementaryB_trans]

theorem B_fieldEquiv_symm (n : ℕ) (e : F ≃+* K) :
    B_fieldEquiv n e.symm = (B_fieldEquiv n e).symm := by
  ext g
  apply (B_fieldEquiv n e).injective
  have h := congrArg (fun z : B n K ≃* B n K => z g)
    (B_fieldEquiv_trans n e.symm e)
  simpa [B_fieldEquiv_refl] using h.symm

theorem B_equiv_of_card_eq [Finite F] [Finite K] (n : ℕ) (_hn : 2 ≤ n)
    (h : Nat.card F = Nat.card K) : Nonempty (B n F ≃* B n K) := by
  letI := Fintype.ofFinite F
  letI := Fintype.ofFinite K
  let e : F ≃+* K := FiniteField.ringEquivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using h)
  exact ⟨B_fieldEquiv n e⟩

end Atlas.Orthogonal
