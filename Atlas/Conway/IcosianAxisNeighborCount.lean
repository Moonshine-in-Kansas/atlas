import Atlas.Conway.IcosianAxisRootGeometry

noncomputable section
namespace Atlas.Conway
open Atlas.Lattices

/-- Actual quaternionic root lines perpendicular to the first coordinate axis. -/
abbrev IcosianAxisNeighbor :=
  {p : IcosianRootPoint // IcosianRootPointOrthogonal (icosianRootAxisPoint 0) p}

def icosianZeroRootToNeighbor (r : IcosianZeroRoot) : IcosianAxisNeighbor :=
  ⟨icosianRootToPoint r.val,(icosianRootAxisPoint_orthogonal_iff 0 r.val).mpr r.property⟩

theorem icosianZeroRootToNeighbor_surjective : Function.Surjective icosianZeroRootToNeighbor := by
  rintro ⟨p,hp⟩
  obtain ⟨r,hr⟩ := icosianRootToPoint_surjective p
  have hz : r.val 0=0 := (icosianRootAxisPoint_orthogonal_iff 0 r).mp (hr.symm ▸ hp)
  exact ⟨⟨r,hz⟩,Subtype.ext hr⟩

def icosianZeroRootNeighborFiberEquiv (p : IcosianAxisNeighbor) :
    {r : IcosianZeroRoot // icosianZeroRootToNeighbor r=p} ≃
      {r : IcosianRoot // icosianRootToPoint r=p.val} where
  toFun r := ⟨r.val.val,congrArg Subtype.val r.property⟩
  invFun r := ⟨⟨r.val,(icosianRootAxisPoint_orthogonal_iff 0 r.val).mp (r.property.symm ▸ p.property)⟩,
    Subtype.ext r.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem icosianZeroRootNeighbor_fiber_card (p : IcosianAxisNeighbor) :
    Nat.card {r : IcosianZeroRoot // icosianZeroRootToNeighbor r=p}=120 := by
  rw [Nat.card_congr (icosianZeroRootNeighborFiberEquiv p),icosianRootToPoint_fiber_card]

/-- The first coordinate root line has exactly ten perpendicular root lines.
This uses the independent1200-root coordinate-plane count and proved120-root line saturation. -/
theorem icosianAxisNeighbors_card : Nat.card IcosianAxisNeighbor=10 := by
  letI : Finite IcosianZeroRoot := Nat.finite_of_card_ne_zero (by rw [icosianZeroRoots_card]; decide)
  letI : Finite IcosianAxisNeighbor := Finite.of_surjective _ icosianZeroRootToNeighbor_surjective
  letI : Fintype IcosianAxisNeighbor := Fintype.ofFinite _
  have he := Nat.card_congr (Equiv.sigmaPreimageEquiv icosianZeroRootToNeighbor)
  rw [Nat.card_sigma] at he
  change (∑ p : IcosianAxisNeighbor, Nat.card {r : IcosianZeroRoot // icosianZeroRootToNeighbor r=p})=
    Nat.card IcosianZeroRoot at he
  simp_rw [icosianZeroRootNeighbor_fiber_card] at he
  rw [Finset.sum_const,Finset.card_univ,← Nat.card_eq_fintype_card,icosianZeroRoots_card] at he
  simp only [nsmul_eq_mul,Nat.cast_id] at he
  omega

end Atlas.Conway
