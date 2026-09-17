import Atlas.Conway.EisensteinCoordinateFrame

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

/-- Every signed code-phase and pure M11 parameter preserves the actual 72-vector frame. -/
theorem eisensteinMonomialParameter_frame_forward (p : EisensteinMonomialParameters)
    (z : EisensteinRationalCoordinates) (hz : z ∈ eisensteinCoordinateFrame) :
    (eisensteinMonomialParameterIsometry p).val z ∈ eisensteinCoordinateFrame := by
  obtain ⟨⟨i,v⟩,rfl⟩ := hz
  let σ := p.2.2.val
  let u := eisensteinSignedPhaseUnit p.1 (p.2.1.val (σ i))
  refine ⟨(σ i,u*v),?_⟩
  funext j
  rw [eisensteinMonomialParameterIsometry_apply]
  by_cases hj : j=σ i
  · subst j
    simp only [eisensteinFrameVector,σ,Pi.single_eq_same,Equiv.symm_apply_apply]
    change eisensteinFrameScale*eisensteinToRational ((u*v : Eisensteinˣ) : Eisenstein) =
      eisensteinToRational (eisensteinSignedPhase p.1 (p.2.1.val (σ i))) *
        (eisensteinFrameScale*eisensteinToRational (v : Eisenstein))
    simp only [Units.val_mul,map_mul,u,eisensteinSignedPhaseUnit_val]
    ring
  · have hi : σ.symm j ≠ i := by
      intro h
      have he := congrArg σ h
      simp only [Equiv.apply_symm_apply] at he
      exact hj he
    simp [eisensteinFrameVector,Pi.single_apply,hj,hi,σ]

theorem eisensteinFrame_iff_of_forward (f : eisensteinHermitianGroup)
    (hf : ∀ z ∈ eisensteinCoordinateFrame, f.val z ∈ eisensteinCoordinateFrame) :
    ∀ z, z ∈ eisensteinCoordinateFrame ↔ f.val z ∈ eisensteinCoordinateFrame := by
  letI : Finite eisensteinCoordinateFrame :=
    (Nat.card_pos_iff.mp (show 0 < Nat.card eisensteinCoordinateFrame by
      rw [eisensteinCoordinateFrame_card]; decide)).2
  let r : eisensteinCoordinateFrame → eisensteinCoordinateFrame := fun z => ⟨f.val z.val,hf _ z.prop⟩
  have hr : Function.Injective r := by
    intro z w h
    exact Subtype.ext (f.val.injective (congrArg Subtype.val h))
  intro z
  refine ⟨hf z,?_⟩
  intro hz
  obtain ⟨w,hw⟩ := Finite.surjective_of_injective hr ⟨f.val z,hz⟩
  have he : w.val=z := f.val.injective (congrArg Subtype.val hw)
  exact he ▸ w.prop

def eisensteinFrameFromParameters (p : EisensteinMonomialParameters) :
    eisensteinCoordinateFrameStabilizer :=
  ⟨eisensteinMonomialParameterIsometry p,
    eisensteinFrame_iff_of_forward _ (eisensteinMonomialParameter_frame_forward p)⟩

theorem eisensteinFrameFromParameters_injective : Function.Injective eisensteinFrameFromParameters := by
  intro p q h
  exact eisensteinMonomialParameterIsometry_injective (congrArg Subtype.val h)

theorem eisensteinFrameFromParameters_surjective : Function.Surjective eisensteinFrameFromParameters := by
  intro f
  obtain ⟨d,hd⟩ := eisensteinCoordinateFrame_integral_monomial f
  obtain ⟨p,hp⟩ := eisensteinMonomialFromParameters_surjective d
  refine ⟨p,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  funext i
  change (eisensteinMonomialParameterIsometry p).val z i = f.val.val z i
  rw [eisensteinMonomialParameterIsometry_apply,hd,← hp]
  simp only [eisensteinMonomialFromParameters,eisensteinSignedPhaseUnit_val]

def eisensteinFullFrameParameterEquiv : EisensteinMonomialParameters ≃
    eisensteinCoordinateFrameStabilizer :=
  Equiv.ofBijective eisensteinFrameFromParameters
    ⟨eisensteinFrameFromParameters_injective,eisensteinFrameFromParameters_surjective⟩

/-- The order is for the full frame stabilizer in the full Hermitian group. -/
theorem eisensteinFullFrameStabilizer_order : Nat.card eisensteinCoordinateFrameStabilizer = 11547360 := by
  rw [← Nat.card_congr eisensteinFullFrameParameterEquiv]
  exact (Nat.card_congr eisensteinMonomialParameterEquiv).trans eisensteinMonomialDatum_card

def eisensteinFrameToCo0 : eisensteinCoordinateFrameStabilizer →* LeechIsometryGroup :=
  eisensteinHermitianToCo0.comp eisensteinCoordinateFrameStabilizer.subtype

theorem eisensteinFrameToCo0_injective : Function.Injective eisensteinFrameToCo0 :=
  eisensteinHermitianToCo0_injective.comp eisensteinCoordinateFrameStabilizer.subtype_injective

theorem eisensteinFrameToCo0_agrees (f : eisensteinCoordinateFrameStabilizer)
    (z : EisensteinRationalCoordinates) :
    (fullIsometryEquiv (eisensteinFrameToCo0 f)).val (eisensteinComparison z) =
      eisensteinComparison (f.val.val z) :=
  eisensteinCentralizerEquiv_agrees f.val z

end Atlas.Conway
