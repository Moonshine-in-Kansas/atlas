import Atlas.Lattices.EisensteinComparisonRotation
import Atlas.Lattices.EisensteinRotationLattice
import Atlas.Lattices.EisensteinComparisonLattice
import Atlas.Lattices.LeechFullIsometries

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes

/-- The scalar rotation preserves the actual rational image of the Golay Leech lattice. -/
theorem eisensteinRationalRotation_lattice_iff (x : RationalCoordinates) :
    x ∈ rationalLeech ↔ eisensteinRationalRotation x ∈ rationalLeech := by
  have hc := eisensteinComparison_lattice_iff (eisensteinComparison.symm x)
  have hr := eisensteinRotation_lattice_iff (eisensteinComparison.symm x)
  have ht := eisensteinComparison_lattice_iff
    (eisensteinRotation (eisensteinComparison.symm x))
  simpa only [LinearEquiv.apply_symm_apply, eisensteinRationalRotation_apply] using
    hc.symm.trans (hr.trans ht)

/-- The actual rational lattice isometry defined by the Eisenstein scalar. -/
def eisensteinRationalLatticeRotation : rationalLatticeIsometries :=
  ⟨eisensteinRationalRotation, eisensteinRationalRotation_form,
    eisensteinRationalRotation_lattice_iff⟩

/-- The distinguished order-three isometry of the retained integral Leech lattice. -/
def eisensteinRho : LeechIsometryGroup :=
  fullIsometryEquiv.symm eisensteinRationalLatticeRotation

theorem eisensteinRho_extension :
    fullIsometryEquiv eisensteinRho = eisensteinRationalLatticeRotation :=
  fullIsometryEquiv.apply_symm_apply _

/-- The integral scalar isometry agrees with its explicitly conjugated rational action. -/
theorem eisensteinRho_agrees (x : leech) :
    rationalEmbedding (eisensteinRho.val x).val =
      eisensteinRationalRotation (rationalEmbedding x.val) := by
  have h := congrArg (fun g : rationalLatticeIsometries =>
    g.val (rationalEmbedding x.val)) eisensteinRho_extension
  change rationalExtension eisensteinRho.val (rationalEmbedding x.val) = _ at h
  rw [rationalExtension_agrees] at h
  exact h

theorem eisensteinRho_cube : eisensteinRho ^ 3 = 1 := by
  apply fullIsometryEquiv.injective
  rw [map_pow, map_one, eisensteinRho_extension]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact eisensteinRationalRotation_cube x

/-- The polynomial identity holds on the actual integral Leech lattice. -/
theorem eisensteinRho_polynomial (x : leech) :
    eisensteinRho.val (eisensteinRho.val x) + eisensteinRho.val x + x = 0 := by
  apply Subtype.ext
  apply rationalEmbedding_injective
  simp only [Submodule.coe_add, Submodule.coe_zero, map_add, map_zero]
  simp only [eisensteinRho_agrees]
  exact eisensteinRationalRotation_polynomial (rationalEmbedding x.val)

/-- The actual integral scalar has no nonzero fixed lattice vector. -/
theorem eisensteinRho_fixed_iff (x : leech) :
    eisensteinRho.val x = x ↔ x = 0 := by
  constructor
  · intro h
    have hr := congrArg (fun y : leech => rationalEmbedding y.val) h
    rw [eisensteinRho_agrees] at hr
    have hz := (eisensteinRationalRotation_fixed_iff _).mp hr
    apply Subtype.ext
    apply rationalEmbedding_injective
    simpa using hz
  · rintro rfl; exact eisensteinRho.val.map_zero

/-- Exact order three for the actual lattice isometry. -/
theorem eisensteinRho_order : orderOf eisensteinRho = 3 := by
  apply orderOf_eq_prime
  · exact eisensteinRho_cube
  · intro h
    have he := eisensteinRho_extension
    rw [h, map_one] at he
    have hr := congrArg (fun g : rationalLatticeIsometries =>
      g.val (fun _ => (1 : ℚ))) he
    have hz := (eisensteinRationalRotation_fixed_iff (fun _ => 1)).mp hr.symm
    have hi := congrFun hz ((0,0),0)
    exact one_ne_zero hi

end Atlas.Conway
