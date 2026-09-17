import Atlas.Conway.EisensteinScalars
import Atlas.Conway.EisensteinFrameAction
import Atlas.Conway.EisensteinFrameNorms

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def eisensteinIntegralFrameVector (p : Fin 12 × Eisensteinˣ) : EisensteinLattice :=
  ⟨Pi.single p.1 ((3*eisensteinTheta)*(p.2 : Eisenstein)),
    (eisensteinLeechModule_axis_iff _ _).mpr ⟨p.2,rfl⟩⟩

theorem eisensteinIntegralFrameVector_embedding (p : Fin 12 × Eisensteinˣ) :
    eisensteinCoordinateEmbedding (eisensteinIntegralFrameVector p).val = eisensteinFrameVector p := by
  funext i
  by_cases hi : i=p.1 <;>
    simp [eisensteinIntegralFrameVector,eisensteinCoordinateEmbedding,eisensteinFrameVector,
      eisensteinFrameScale,Pi.single_apply,hi]

def eisensteinFrameShellVector (p : Fin 12 × Eisensteinˣ) : EisensteinShell 6 :=
  ⟨eisensteinIntegralFrameVector p,by
    unfold eisensteinNorm
    rw [eisensteinIntegralFrameVector_embedding]
    exact eisensteinCoordinateFrame_norm_six _ ⟨p,rfl⟩⟩

def eisensteinStandardFrame : EisensteinFrame :=
  eisensteinFrameOfVector (eisensteinFrameShellVector (0,1))

theorem eisensteinIntegralFrameVector_class (i : Fin 12) :
    eisensteinClass (eisensteinIntegralFrameVector (i,1)) =
      eisensteinClass (eisensteinIntegralFrameVector (0,1)) := by
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨⟨eisensteinDifferenceGenerator i,eisensteinDifferenceGenerator_mem i⟩,?_⟩
  apply Subtype.ext
  funext j
  change eisensteinTheta * eisensteinDifferenceGenerator i j =
    (eisensteinIntegralFrameVector (i,1)).val j - (eisensteinIntegralFrameVector (0,1)).val j
  simp only [eisensteinDifferenceGenerator,eisensteinIntegralFrameVector,Units.val_one,
    mul_one,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
  simp only [Pi.single_apply]
  split_ifs <;> ring

theorem eisensteinClass_phase (a : ZMod 3) (x : EisensteinLattice) :
    eisensteinClass (eisensteinPhase a • x) = eisensteinClass x := by
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨eisensteinPhaseCorrection a • x,?_⟩
  apply Subtype.ext
  funext i
  change eisensteinTheta * (eisensteinPhaseCorrection a * x.val i) =
    eisensteinPhase a * x.val i - x.val i
  rw [← mul_assoc]
  have h := eisensteinPhase_correction a
  rw [h]
  ring

theorem eisensteinClass_unit_pair (u : Eisensteinˣ) (x : EisensteinLattice) :
    eisensteinFramePair (eisensteinClass ((u : Eisenstein) • x)) =
      eisensteinFramePair (eisensteinClass x) := by
  obtain ⟨a,rfl⟩ := eisensteinScalarUnitHom_surjective u
  change eisensteinFramePair (eisensteinClass
    ((eisensteinSignedPhaseUnit (decide (a.1.toAdd≠0)) a.2.toAdd : Eisenstein) • x)) = _
  rw [eisensteinSignedPhaseUnit_val]
  unfold eisensteinSignedPhase
  split_ifs
  · rw [neg_smul,map_neg,eisensteinClass_phase,eisensteinFramePair_neg]
  · rw [eisensteinClass_phase]

theorem eisensteinFrameShellVector_standard (p : Fin 12 × Eisensteinˣ) :
    eisensteinFrameOfVector (eisensteinFrameShellVector p) = eisensteinStandardFrame := by
  apply Subtype.ext
  change eisensteinFramePair (eisensteinClass (eisensteinIntegralFrameVector p)) = _
  have he : eisensteinIntegralFrameVector p = (p.2 : Eisenstein) • eisensteinIntegralFrameVector (p.1,1) := by
    apply Subtype.ext
    funext i
    by_cases hi : i=p.1 <;>
      simp [eisensteinIntegralFrameVector,Pi.single_apply,hi,Pi.smul_apply,mul_comm]
  rw [he,eisensteinClass_unit_pair,eisensteinIntegralFrameVector_class]
  rfl


theorem eisensteinFrameShellVector_injective : Function.Injective eisensteinFrameShellVector := by
  intro p q h
  apply eisensteinFrameVector_injective
  have he := congrArg (fun x : EisensteinShell 6 => eisensteinCoordinateEmbedding x.val.val) h
  simpa only [eisensteinFrameShellVector,eisensteinIntegralFrameVector_embedding] using he

theorem eisensteinStandardFrame_vectors :
    ∀ x : EisensteinShell 6, x ∈ eisensteinFrameVectors eisensteinStandardFrame ↔
      ∃ p, eisensteinFrameShellVector p = x := by
  letI : Finite Eisensteinˣ := Nat.finite_of_card_ne_zero (by rw [eisenstein_units_card]; decide)
  letI : Fintype Eisensteinˣ := Fintype.ofFinite _
  let S := Finset.univ.image eisensteinFrameShellVector
  have hsub : S ⊆ eisensteinFrameVectors eisensteinStandardFrame := by
    intro x hx
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [← eisensteinFrameShellVector_standard p]
    change eisensteinClass (eisensteinIntegralFrameVector p) ∈
      eisensteinFramePair (eisensteinClass (eisensteinIntegralFrameVector p))
    simp [eisensteinFramePair]
  have hcard : S.card = 72 := by
    rw [Finset.card_image_of_injective _ eisensteinFrameShellVector_injective,Finset.card_univ,
      Fintype.card_prod,Fintype.card_fin,← Nat.card_eq_fintype_card,eisenstein_units_card]
  have he : S = eisensteinFrameVectors eisensteinStandardFrame :=
    Finset.eq_of_subset_of_card_le hsub (by rw [eisensteinFrameVectors_card,hcard])
  intro x
  rw [← he]
  simp [S]

/-- Intrinsic standard-frame vectors are exactly the 72 coordinate-unit vectors. -/
theorem eisensteinStandardFrame_coordinate_iff (x : EisensteinShell 6) :
    x ∈ eisensteinFrameVectors eisensteinStandardFrame ↔
      eisensteinCoordinateEmbedding x.val.val ∈ eisensteinCoordinateFrame := by
  rw [eisensteinStandardFrame_vectors]
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨p,(eisensteinIntegralFrameVector_embedding p).symm⟩
  · rintro ⟨p,hp⟩
    refine ⟨p,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply eisensteinCoordinateEmbedding_injective
    exact (eisensteinIntegralFrameVector_embedding p).trans hp


/-- The previously computed full monomial stabilizer is exactly the stabilizer
of the intrinsic standard frame under the full Hermitian lattice group. -/
theorem eisensteinStandardFrame_stabilizer :
    MulAction.stabilizer eisensteinHermitianGroup eisensteinStandardFrame =
      eisensteinCoordinateFrameStabilizer := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hg
    apply eisensteinFrame_iff_of_forward
    intro z hz
    obtain ⟨p,rfl⟩ := hz
    have hx : eisensteinFrameShellVector p ∈ eisensteinFrameVectors eisensteinStandardFrame :=
      (eisensteinStandardFrame_vectors _).mpr ⟨p,rfl⟩
    have hy : eisensteinShellAction g 6 (eisensteinFrameShellVector p) ∈
        eisensteinFrameVectors eisensteinStandardFrame := by
      rw [← hg,eisensteinFrameAction_vectors]
      exact Finset.mem_image.mpr ⟨_,hx,rfl⟩
    have hyc := (eisensteinStandardFrame_coordinate_iff _).mp hy
    change eisensteinCoordinateEmbedding (eisensteinIntegralAction g (eisensteinIntegralFrameVector p)).val ∈ _ at hyc
    rw [eisensteinIntegralAction_agrees,eisensteinIntegralFrameVector_embedding] at hyc
    exact hyc
  · intro hg
    apply eisensteinFrameVectors_injective
    rw [eisensteinFrameAction_vectors]
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      apply (eisensteinStandardFrame_coordinate_iff _).mpr
      have hxc := (eisensteinStandardFrame_coordinate_iff x).mp hx
      change eisensteinCoordinateEmbedding (eisensteinIntegralAction g x.val).val ∈ _
      rw [eisensteinIntegralAction_agrees]
      exact (hg _).mp hxc
    · rw [Finset.card_image_of_injective _ (eisensteinShellAction g 6).injective]

theorem eisensteinStandardFrame_stabilizer_order :
    Nat.card (MulAction.stabilizer eisensteinHermitianGroup eisensteinStandardFrame) = 11547360 := by
  rw [eisensteinStandardFrame_stabilizer]
  exact eisensteinFullFrameStabilizer_order

end Atlas.Conway
