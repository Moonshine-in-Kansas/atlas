import Atlas.Conway.EisensteinRotation
import Atlas.LinearAlgebra.AutomorphismCongr

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.LinearAlgebra

/-- All scalar-linear Hermitian isometries preserving the actual Eisenstein lattice.
The ambient rational-linear representation does not restrict the group: scalar
linearity, preservation of the full Hermitian form and both lattice containments
are explicit defining conditions. -/
def eisensteinHermitianGroup :
    Subgroup (EisensteinRationalCoordinates ≃ₗ[ℚ] EisensteinRationalCoordinates) where
  carrier := {f | (∀ a : EisensteinRational, ∀ z, f (a • z) = a • f z) ∧
    (∀ z w, eisensteinHermitian (f z) (f w) = eisensteinHermitian z w) ∧
    ∀ z, z ∈ rationalEisensteinLattice ↔ f z ∈ rationalEisensteinLattice}
  one_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => Iff.rfl⟩
  mul_mem' := by
    rintro f g ⟨hf, hfH, hfL⟩ ⟨hg, hgH, hgL⟩
    refine ⟨fun a z => ?_, fun z w => ?_, fun z => ?_⟩
    · change f (g (a • z)) = a • f (g z)
      rw [hg, hf]
    · change eisensteinHermitian (f (g z)) (f (g w)) = _
      rw [hfH, hgH]
    · exact (hgL z).trans (hfL (g z))
  inv_mem' := by
    rintro f ⟨hf, hfH, hfL⟩
    refine ⟨fun a z => ?_, fun z w => ?_, fun z => ?_⟩
    · change f.symm (a • z) = a • f.symm z
      apply f.injective
      rw [f.apply_symm_apply, hf, f.apply_symm_apply]
    · have h := hfH (f.symm z) (f.symm w)
      change eisensteinHermitian (f.symm z) (f.symm w) = _
      simpa only [LinearEquiv.apply_symm_apply] using h.symm
    · have h := hfL (f.symm z)
      change z ∈ rationalEisensteinLattice ↔ f.symm z ∈ rationalEisensteinLattice
      simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- The full centralizer of the actual integral scalar isometry in Co0. -/
def eisensteinCentralizer : Subgroup LeechIsometryGroup :=
  Subgroup.centralizer {eisensteinRho}

/-- Explicit transport between the two full rational automorphism groups. -/
def eisensteinAutomorphismComparison := linearAutomorphismCongr eisensteinComparison

@[simp] theorem eisensteinAutomorphismComparison_rotation :
    eisensteinAutomorphismComparison eisensteinRotationEquiv = eisensteinRationalRotation := rfl

/-- Exact characterization, not merely an embedding: a rational transformation
is scalar-linear and Hermitian exactly when its real transport is a lattice
isometry commuting with the distinguished scalar rotation. -/
theorem eisensteinHermitianGroup_iff
    (f : EisensteinRationalCoordinates ≃ₗ[ℚ] EisensteinRationalCoordinates) :
    f ∈ eisensteinHermitianGroup ↔
      eisensteinAutomorphismComparison f ∈ rationalLatticeIsometries ∧
      eisensteinAutomorphismComparison f * eisensteinRationalRotation =
        eisensteinRationalRotation * eisensteinAutomorphismComparison f := by
  have hcomm : eisensteinAutomorphismComparison f * eisensteinRationalRotation =
      eisensteinRationalRotation * eisensteinAutomorphismComparison f ↔
      ∀ z, f (eisensteinRotation z) = eisensteinRotation (f z) := by
    rw [← eisensteinAutomorphismComparison_rotation, ← map_mul, ← map_mul]
    rw [eisensteinAutomorphismComparison.injective.eq_iff]
    exact LinearEquiv.ext_iff
  constructor
  · rintro ⟨hlin, hH, hL⟩
    refine ⟨⟨fun x y => ?_, fun x => ?_⟩, hcomm.mpr (fun z => hlin rationalOmega z)⟩
    · change rationalForm (eisensteinComparison (f (eisensteinComparison.symm x)))
        (eisensteinComparison (f (eisensteinComparison.symm y))) = _
      rw [eisensteinComparison_isometry]
      unfold eisensteinBilinear
      rw [hH]
      have h := eisensteinComparison_isometry
        (eisensteinComparison.symm x) (eisensteinComparison.symm y)
      change rationalForm (eisensteinComparison (eisensteinComparison.symm x))
        (eisensteinComparison (eisensteinComparison.symm y)) = _ at h
      change eisensteinBilinear (eisensteinComparison.symm x) (eisensteinComparison.symm y) = _
      simpa only [LinearEquiv.apply_symm_apply] using h.symm
    · have h := (eisensteinComparison_lattice_iff (eisensteinComparison.symm x)).symm.trans
        ((hL (eisensteinComparison.symm x)).trans
          (eisensteinComparison_lattice_iff (f (eisensteinComparison.symm x))))
      change x ∈ rationalLeech ↔ eisensteinComparison (f (eisensteinComparison.symm x)) ∈ rationalLeech
      simpa only [LinearEquiv.apply_symm_apply] using h
  · rintro ⟨⟨hB, hL⟩, hc⟩
    have hc' := hcomm.mp hc
    have hf : ∀ z w, eisensteinBilinear (f z) (f w) = eisensteinBilinear z w := by
      intro z w
      have h := hB (eisensteinComparison z) (eisensteinComparison w)
      change rationalForm
        (eisensteinComparison (f (eisensteinComparison.symm (eisensteinComparison z))))
        (eisensteinComparison (f (eisensteinComparison.symm (eisensteinComparison w)))) = _ at h
      simpa only [LinearEquiv.symm_apply_apply, eisensteinComparison_isometry] using h
    refine ⟨eisensteinLinear_of_rotation f.toLinearMap hc',
      eisensteinHermitian_of_real_and_rotation f hf hc', fun z => ?_⟩
    have h := (eisensteinComparison_lattice_iff z).trans (hL (eisensteinComparison z))
    have ht := eisensteinComparison_lattice_iff (f z)
    change z ∈ rationalEisensteinLattice ↔
      eisensteinComparison (f (eisensteinComparison.symm (eisensteinComparison z))) ∈ rationalLeech at h
    rw [LinearEquiv.symm_apply_apply] at h
    exact h.trans ht.symm

/-- Transport of the full Hermitian lattice group into the rational Leech isometry group. -/
def eisensteinHermitianToRational : eisensteinHermitianGroup →* rationalLatticeIsometries where
  toFun f := ⟨eisensteinAutomorphismComparison f.val, (eisensteinHermitianGroup_iff f.val).mp f.property |>.1⟩
  map_one' := by apply Subtype.ext; exact map_one eisensteinAutomorphismComparison
  map_mul' f g := by apply Subtype.ext; exact map_mul eisensteinAutomorphismComparison f.val g.val

/-- The actual integral isometry associated to every full Hermitian lattice isometry. -/
def eisensteinHermitianToCo0 : eisensteinHermitianGroup →* LeechIsometryGroup :=
  fullIsometryEquiv.symm.toMonoidHom.comp eisensteinHermitianToRational

theorem eisensteinHermitianToCo0_extension (f : eisensteinHermitianGroup) :
    fullIsometryEquiv (eisensteinHermitianToCo0 f) = eisensteinHermitianToRational f :=
  fullIsometryEquiv.apply_symm_apply _

theorem eisensteinHermitianToCo0_injective : Function.Injective eisensteinHermitianToCo0 := by
  intro f g h
  apply Subtype.ext
  apply eisensteinAutomorphismComparison.injective
  have hr := congrArg (fun k : LeechIsometryGroup => (fullIsometryEquiv k).val) h
  rw [eisensteinHermitianToCo0_extension, eisensteinHermitianToCo0_extension] at hr
  exact hr

/-- Every transported Hermitian lattice isometry centralizes the actual scalar. -/
theorem eisensteinHermitianToCo0_mem (f : eisensteinHermitianGroup) :
    eisensteinHermitianToCo0 f ∈ eisensteinCentralizer := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply fullIsometryEquiv.injective
  rw [map_mul, map_mul, eisensteinRho_extension]
  rw [eisensteinHermitianToCo0_extension]
  apply Subtype.ext
  change eisensteinAutomorphismComparison f.val * eisensteinRationalRotation = _
  exact (eisensteinHermitianGroup_iff f.val).mp f.property |>.2

/-- Every element of the actual centralizer arises from a full Hermitian lattice isometry. -/
theorem eisensteinHermitianToCo0_surjective_centralizer
    (g : eisensteinCentralizer) : ∃ f, eisensteinHermitianToCo0 f = g.val := by
  let r := fullIsometryEquiv g.val
  let f := eisensteinAutomorphismComparison.symm r.val
  have hf : f ∈ eisensteinHermitianGroup := by
    apply (eisensteinHermitianGroup_iff f).mpr
    have he : eisensteinAutomorphismComparison f = r.val :=
      eisensteinAutomorphismComparison.apply_symm_apply _
    rw [he]
    refine ⟨r.property, ?_⟩
    have hc := Subgroup.mem_centralizer_singleton_iff.mp g.property
    have h := congrArg fullIsometryEquiv hc
    rw [map_mul, map_mul, eisensteinRho_extension] at h
    exact congrArg Subtype.val h
  refine ⟨⟨f, hf⟩, ?_⟩
  apply fullIsometryEquiv.injective
  rw [eisensteinHermitianToCo0_extension]
  apply Subtype.ext
  change eisensteinAutomorphismComparison f = r.val
  exact eisensteinAutomorphismComparison.apply_symm_apply r.val

/-- Exact image equality with the full centralizer inside the actual Co0 model. -/
theorem eisensteinHermitianToCo0_range :
    eisensteinHermitianToCo0.range = eisensteinCentralizer := by
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨f, rfl⟩; exact eisensteinHermitianToCo0_mem f
  · intro hg
    obtain ⟨f, hf⟩ := eisensteinHermitianToCo0_surjective_centralizer ⟨g, hg⟩
    exact ⟨f, hf⟩

/-- The full scalar-linear Hermitian lattice group is exactly the actual Co0 centralizer. -/
def eisensteinCentralizerEquiv : eisensteinHermitianGroup ≃* eisensteinCentralizer :=
  (MonoidHom.ofInjective eisensteinHermitianToCo0_injective).trans
    (MulEquiv.subgroupCongr eisensteinHermitianToCo0_range)

@[simp] theorem eisensteinCentralizerEquiv_apply_val (f : eisensteinHermitianGroup) :
    (eisensteinCentralizerEquiv f).val = eisensteinHermitianToCo0 f := rfl

/-- The exact identification is compatible with the explicit lattice comparison. -/
theorem eisensteinCentralizerEquiv_agrees
    (f : eisensteinHermitianGroup) (z : EisensteinRationalCoordinates) :
    (fullIsometryEquiv (eisensteinCentralizerEquiv f).val).val (eisensteinComparison z) =
      eisensteinComparison (f.val z) := by
  rw [eisensteinCentralizerEquiv_apply_val, eisensteinHermitianToCo0_extension]
  change eisensteinComparison (f.val (eisensteinComparison.symm (eisensteinComparison z))) = _
  rw [LinearEquiv.symm_apply_apply]

end Atlas.Conway
