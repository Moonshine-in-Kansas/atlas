import Atlas.Fischer.RootRays
import Atlas.Fischer.ReflectingRootPairing
import Atlas.Fischer.ScalarAutomorphisms

noncomputable section
namespace Atlas.Fischer

/-- Cubic phases preserve the full intrinsic reflecting-root conditions. -/
theorem reflectingRoot_phase (r : Coordinates) (hr : IsReflectingRoot r)
    (a : Scalar) (ha : a^3=1) : IsReflectingRoot (a • r) := by
  have ha2 : (a^2)^3=1 := by rw [← pow_mul,Nat.mul_comm 2 3,pow_mul,ha]; simp
  let z : Mu3 := rootsOfUnity.mkOfPowEq (a^2) ha2
  have hm (x : Coordinates) : rootMap (a • r) x=scalarPhaseEquiv z (rootMap r x) :=
    rootMap_phase r x a ha
  refine ⟨root_phase r hr.1 a ha,?_,?_,?_⟩
  · intro x y
    rw [hm,hm,scalarPhaseEquiv_hermitian,hr.2.1]
  · intro x
    simp only [rootMap_phase r _ a ha,rootMap_smul,hr.2.2.1 x,smul_smul]
    rw [mul_comm,cube_root_unit_norm ha2,one_smul]
  · intro x y
    rw [hm,hr.2.2.2,hm,hm,scalarPhaseEquiv_product]

/-- Every member of the actual three-element normalized ray is reflecting. -/
theorem rootRay_members_are_reflecting (r : Coordinates) (hr : IsReflectingRoot r)
    {x : Coordinates} (hx : x ∈ rootRay r) : IsReflectingRoot x := by
  obtain ⟨a,ha,rfl⟩ := (mem_rootRay r x).mp hx
  exact reflectingRoot_phase r hr a ha

/-- The intrinsic pairing theorem stated directly for distinct normalized rays. -/
theorem reflectingRoot_distinct_ray_pairing (r s : Coordinates)
    (hr : IsReflectingRoot r) (hs : IsReflectingRoot s)
    (hd : rootRay s ≠ rootRay r) :
    hermitian r s=0 ∨ ∃ a : Mu3, hermitian r s=(a.val.val : Scalar) := by
  apply reflectingRoot_pairing_zero_or_mu3 r s hr hs
  intro h
  exact hd ((rootRay_eq_iff_mu3 r s).mpr h)

end Atlas.Fischer
