import Atlas.Fischer.RootPhases

noncomputable section
namespace Atlas.Fischer

/-- A normalized ray consists of precisely the three cubic scalar phases. -/
def rootRay (r : Coordinates) : Finset Coordinates := by
  classical
  exact cubeRootValues.image (fun a => a • r)

theorem mem_rootRay (r x : Coordinates) :
    x ∈ rootRay r ↔ ∃ a : Scalar, a^3=1 ∧ x=a • r := by
  classical
  simp only [rootRay,Finset.mem_image,mem_cubeRootValues]
  constructor
  · rintro ⟨a,ha,hax⟩
    exact ⟨a,ha,hax.symm⟩
  · rintro ⟨a,ha,hxa⟩
    exact ⟨a,ha,hxa.symm⟩

theorem mem_rootRay_mu3 (r x : Coordinates) :
    x ∈ rootRay r ↔ ∃ a : Mu3, x=(a.val.val : Scalar) • r := by
  rw [mem_rootRay]
  constructor
  · rintro ⟨a,ha,h⟩
    exact ⟨rootsOfUnity.mkOfPowEq a ha,h⟩
  · rintro ⟨a,h⟩
    exact ⟨a.val.val,(mem_rootsOfUnity' _ _).mp a.property,h⟩

theorem root_mem_rootRay (r : Coordinates) : r ∈ rootRay r :=
  (mem_rootRay r r).mpr ⟨1,by simp,by simp⟩

theorem rootRay_card (r : Coordinates) (hr : IsRoot r) : (rootRay r).card=3 := by
  classical
  rw [rootRay,Finset.card_image_of_injective _ (smul_left_injective Scalar (root_ne_zero hr)),
    cubeRootValues_card]

theorem rootRay_phase (r : Coordinates) (a : Scalar) (ha : a^3=1) :
    rootRay (a • r)=rootRay r := by
  classical
  ext x
  simp only [mem_rootRay]
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact ⟨b*a,by rw [mul_pow,hb,ha]; simp,smul_smul b a r⟩
  · rintro ⟨b,hb,rfl⟩
    refine ⟨b*a^2,?_,?_⟩
    · rw [mul_pow,hb,← pow_mul, Nat.mul_comm 2 3,pow_mul,ha]
      simp
    · rw [smul_smul]
      congr 1
      rw [mul_assoc,← pow_succ,ha,mul_one]

theorem rootRay_eq_iff (r s : Coordinates) :
    rootRay s=rootRay r ↔ ∃ a : Scalar, a^3=1 ∧ s=a • r := by
  constructor
  · intro h
    exact (mem_rootRay r s).mp (h ▸ root_mem_rootRay s)
  · rintro ⟨a,ha,rfl⟩
    exact rootRay_phase r a ha

theorem rootRay_eq_iff_mu3 (r s : Coordinates) :
    rootRay s=rootRay r ↔ ∃ a : Mu3, s=(a.val.val : Scalar) • r := by
  rw [rootRay_eq_iff,← mem_rootRay,mem_rootRay_mu3]

theorem rootRay_members_are_roots (r : Coordinates) (hr : IsRoot r)
    {x : Coordinates} (hx : x ∈ rootRay r) : IsRoot x := by
  obtain ⟨a,ha,rfl⟩ := (mem_rootRay r x).mp hx
  exact root_phase r hr a ha

end Atlas.Fischer
