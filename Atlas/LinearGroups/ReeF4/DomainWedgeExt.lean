import Atlas.LinearGroups.ReeF4.DomainWedgeProjection

/-! Agreement on the actual partial domain determines a semilinear map on the
whole polar/cross kernel. The scalar twist is arbitrary but common to both maps. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

/-- No quadratic-isotropy restriction is imposed on either factor. -/
theorem domainWedge_semilinear_ext
    {R : Type*} [Semiring R] (σ : F →+* R)
    {M : Type*} [AddCommMonoid M] [Module R M]
    (f g : StarCarrier (F := F) →ₛₗ[σ] M)
    (h : ∀ (u v : TraceZero F) (huv : StarDomain u v),
      f (domainWedge u v huv) = g (domainWedge u v huv)) : f = g := by
  apply LinearMap.ext
  intro x
  let E : Submodule F (⋀[F]^2 (TraceZero F)) :=
    (LinearMap.eqLocus f g).map (StarCarrier (F := F)).subtype
  have hE : admissibleWedgeSpan (F := F) ≤ E := by
    apply Submodule.span_le.mpr
    rintro w ⟨u, v, huv, rfl⟩
    exact ⟨domainWedge u v huv, h u v huv, rfl⟩
  have hx : x.val ∈ admissibleWedgeSpan (F := F) := by
    rw [admissibleWedgeSpan_eq_starCarrier]
    exact x.property
  obtain ⟨y, hy, he⟩ := hE hx
  have hyx : y = x := Subtype.ext he
  change f y = g y at hy
  simpa only [hyx] using hy

end Atlas.ReeF4
