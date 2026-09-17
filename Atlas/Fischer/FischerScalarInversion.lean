import Atlas.Fischer.GeneratedCentralExtension
import Atlas.Fischer.FullSemilinearQuotient

noncomputable section
namespace Atlas.Fischer

/-- Every conjugate-linear algebra automorphism inverts the cubic scalar
subgroup by actual scalar conjugation on the retained coordinate space. -/
theorem oddSemilinear_scalar_conjugation (g : SemilinearAlgebraAutomorphism)
    (hg : semilinearAlgebraParity g=1) (a : Mu3) :
    g*scalarAlgebraRepresentation a*g⁻¹=scalarAlgebraRepresentation a⁻¹ := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have hs : star (a.val.val : Scalar)=(a.val.val : Scalar)⁻¹ :=
    (inv_eq_of_mul_eq_one_left
      (cube_root_unit_norm ((mem_rootsOfUnity' _ _).mp a.property))).symm
  change g.val ((a.val.val : Scalar) • g.val.symm x)=((a⁻¹).val.val : Scalar) • x
  rw [semilinearAlgebraParity_spec,hg,scalarParityAut_one,hs,Equiv.apply_symm_apply]
  simp

theorem displayedRoot_scalar_conjugation (t : ReflectingRootParameter) (a : Mu3) :
    displayedRootAutomorphism t * scalarAlgebraRepresentation a * (displayedRootAutomorphism t)⁻¹=
      scalarAlgebraRepresentation a⁻¹ := by
  apply oddSemilinear_scalar_conjugation
  exact congrArg Multiplicative.toAdd (displayedAlgebraRootElement_parity t)

/-- The scalar kernel is normal but is not central in the full semilinear
group. Its centrality belongs only to the positive linear subgroup. -/
theorem fullSemilinearScalarKernel_not_central :
    ¬fullSemilinearRayProjection.ker ≤ Subgroup.center SemilinearAlgebraAutomorphism := by
  intro hcentral
  obtain ⟨a,ha,_⟩ := generated_nontrivial_cubic_scalar
  let t : ReflectingRootParameter := .inl (Classical.arbitrary Atlas.Codes.Omega)
  have hz : scalarAlgebraRepresentation a ∈ Subgroup.center SemilinearAlgebraAutomorphism := by
    apply hcentral
    rw [fullSemilinearRayProjection_kernel]
    exact ⟨a,rfl⟩
  have hc := (Subgroup.mem_center_iff.mp hz) (displayedRootAutomorphism t)
  have hi : a⁻¹=a := scalarAlgebraRepresentation_injective (by
    rw [← displayedRoot_scalar_conjugation t a,hc,mul_assoc,mul_inv_cancel,mul_one])
  have h2 : a^2=1 := by
    calc
      a^2 = a*a := pow_two a
      _ = a*a⁻¹ := congrArg (fun z => a*z) hi.symm
      _ = 1 := mul_inv_cancel a
  have h3 : a^3=1 := by
    apply Subtype.ext
    exact a.property
  apply ha
  calc
    a = a^2*a := by rw [h2,one_mul]
    _ = a^3 := (pow_succ a 2).symm
    _ = 1 := h3

end Atlas.Fischer
