import Atlas.LinearGroups.Orthogonal.DFamily
import Atlas.LinearGroups.Orthogonal.ProjectiveFieldTransport
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Specified field transport for the actual public split-D family -/
noncomputable section
namespace Atlas.Orthogonal
variable {F K L : Type*} [Field F] [Field K] [Field L]

/-- The chosen field map acts coordinatewise before descending through the scalar quotient. -/
def DPlus_fieldEquiv (n : ℕ) (e : F ≃+* K) : DPlus n F ≃* DPlus n K :=
  fieldEquivProjectiveElementaryD e

theorem DPlus_fieldEquiv_projection (n : ℕ) (e : F ≃+* K)
    (g : elementarySubgroup (formD n F)) :
    DPlus_fieldEquiv n e (projectiveElementaryMap _ g) =
      projectiveElementaryMap _ (fieldEquivElementaryD e g) := rfl

theorem fieldEquivElementaryD_refl (n : ℕ) (g : elementarySubgroup (formD n F)) :
    fieldEquivElementaryD (RingEquiv.refl F) g = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rfl

theorem fieldEquivElementaryD_trans (n : ℕ) (e : F ≃+* K) (f : K ≃+* L)
    (g : elementarySubgroup (formD n F)) :
    fieldEquivElementaryD (e.trans f) g = fieldEquivElementaryD f (fieldEquivElementaryD e g) := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rfl

theorem DPlus_fieldEquiv_refl (n : ℕ) : DPlus_fieldEquiv n (RingEquiv.refl F) = MulEquiv.refl _ := by
  ext g
  obtain ⟨a,rfl⟩ := projectiveElementaryMap_surjective _ g
  rw [DPlus_fieldEquiv_projection, fieldEquivElementaryD_refl]
  rfl

theorem DPlus_fieldEquiv_trans (n : ℕ) (e : F ≃+* K) (f : K ≃+* L) :
    DPlus_fieldEquiv n (e.trans f) = (DPlus_fieldEquiv n e).trans (DPlus_fieldEquiv n f) := by
  ext g
  obtain ⟨a,rfl⟩ := projectiveElementaryMap_surjective _ g
  change DPlus_fieldEquiv n (e.trans f) (projectiveElementaryMap _ a) =
    DPlus_fieldEquiv n f (DPlus_fieldEquiv n e (projectiveElementaryMap _ a))
  rw [DPlus_fieldEquiv_projection, DPlus_fieldEquiv_projection,
    DPlus_fieldEquiv_projection, fieldEquivElementaryD_trans]

theorem DPlus_fieldEquiv_symm (n : ℕ) (e : F ≃+* K) :
    DPlus_fieldEquiv n e.symm = (DPlus_fieldEquiv n e).symm := by
  ext g
  apply (DPlus_fieldEquiv n e).injective
  have h := congrArg (fun z : DPlus n K ≃* DPlus n K => z g)
    (DPlus_fieldEquiv_trans n e.symm e)
  simpa [DPlus_fieldEquiv_refl] using h.symm

theorem DPlus_equiv_of_card_eq [Finite F] [Finite K] (n : ℕ) (_hn : 4 ≤ n)
    (h : Nat.card F = Nat.card K) : Nonempty (DPlus n F ≃* DPlus n K) := by
  letI := Fintype.ofFinite F
  letI := Fintype.ofFinite K
  let e : F ≃+* K := FiniteField.ringEquivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using h)
  exact ⟨DPlus_fieldEquiv n e⟩

end Atlas.Orthogonal
