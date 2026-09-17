import Atlas.Conway.IcosianRootLines

noncomputable section
namespace Atlas.Conway
open Atlas.Lattices

/-- The root-to-line map has the actual geometric range as codomain. -/
def icosianRootToPoint (r : IcosianRoot) : IcosianRootPoint :=
  ⟨icosianRootPoint r,r,rfl⟩

theorem icosianRootToPoint_surjective : Function.Surjective icosianRootToPoint := by
  rintro ⟨p,r,hr⟩
  exact ⟨r,Subtype.ext hr⟩

def icosianRootPointFiberEquiv (p : IcosianRootPoint) (r : IcosianRoot)
    (hr : icosianRootPoint r=p.val) :
    {s : IcosianRoot // icosianRootToPoint s=p} ≃
      {s : IcosianRoot // icosianRootPoint s=icosianRootPoint r} where
  toFun s := ⟨s.val,(congrArg Subtype.val s.property).trans hr.symm⟩
  invFun s := ⟨s.val,Subtype.ext (s.property.trans hr)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem icosianRootToPoint_fiber_card (p : IcosianRootPoint) :
    Nat.card {s : IcosianRoot // icosianRootToPoint s=p}=120 := by
  obtain ⟨r,hr⟩ := p.property
  rw [Nat.card_congr (icosianRootPointFiberEquiv p r hr),icosianRootLineFiber_card]

/-- Root-line counting from the structural root count and proved scalar saturation. -/
theorem icosianRootPoint_card_of_root_card (h : Nat.card IcosianRoot=37800) :
    Nat.card IcosianRootPoint=315 := by
  letI : Finite IcosianRoot := Nat.finite_of_card_ne_zero (by rw [h]; decide)
  letI : Finite IcosianRootPoint := Finite.of_surjective _ icosianRootToPoint_surjective
  letI : Fintype IcosianRootPoint := Fintype.ofFinite _
  have he := Nat.card_congr (Equiv.sigmaPreimageEquiv icosianRootToPoint)
  rw [Nat.card_sigma] at he
  change (∑ p : IcosianRootPoint, Nat.card {s : IcosianRoot // icosianRootToPoint s=p})=Nat.card IcosianRoot at he
  simp_rw [icosianRootToPoint_fiber_card] at he
  rw [Finset.sum_const,Finset.card_univ,← Nat.card_eq_fintype_card,h] at he
  simp only [nsmul_eq_mul,Nat.cast_id] at he
  omega

end Atlas.Conway
