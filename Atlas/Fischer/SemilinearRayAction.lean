import Atlas.Fischer.ReflectingRayFamily

noncomputable section
namespace Atlas.Fischer
attribute [local instance] Classical.propDecidable

/-- An actual semilinear algebra automorphism transports the whole normalized
three-element ray, including its conjugated scalar phases. -/
theorem semilinearAlgebra_rootRay_map (e : SemilinearAlgebraAutomorphism) (r : Coordinates) :
    (rootRay r).map e.val.toEmbedding = rootRay (e.val r) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy,hxy⟩ := Finset.mem_map.mp hx
    obtain ⟨a,ha,rfl⟩ := (mem_rootRay r y).mp hy
    apply (mem_rootRay (e.val r) x).mpr
    refine ⟨scalarParityAut (semilinearAlgebraParity e) a,?_,?_⟩
    · rw [← map_pow,ha,map_one]
    · exact hxy.symm.trans (semilinearAlgebraParity_spec e a r)
  · intro hx
    obtain ⟨a,ha,rfl⟩ := (mem_rootRay (e.val r) x).mp hx
    apply Finset.mem_map.mpr
    refine ⟨scalarParityAut (semilinearAlgebraParity e) a • r,?_,?_⟩
    · apply (mem_rootRay r _).mpr
      refine ⟨_,?_,rfl⟩
      rw [← map_pow,ha,map_one]
    · change e.val (_ • r) = a • e.val r
      rw [semilinearAlgebraParity_spec,scalarParityAut_involutive]

def semilinearDisplayedRayMap (e : SemilinearAlgebraAutomorphism)
    (R : DisplayedReflectingRay) : DisplayedReflectingRay :=
  ⟨R.val.map e.val.toEmbedding,by
    obtain ⟨t,ht⟩ := R.property
    obtain ⟨s,hs⟩ := reflectingRootParameter_automorphism e t
    refine ⟨s,?_⟩
    rw [← ht]
    exact hs.symm.trans (semilinearAlgebra_rootRay_map e (reflectingRootParameterVector t)).symm⟩

theorem semilinearDisplayedRayMap_one (R : DisplayedReflectingRay) :
    semilinearDisplayedRayMap 1 R=R := by
  apply Subtype.ext
  change R.val.map (Function.Embedding.refl Coordinates)=R.val
  exact Finset.map_refl

theorem semilinearDisplayedRayMap_mul (e f : SemilinearAlgebraAutomorphism)
    (R : DisplayedReflectingRay) :
    semilinearDisplayedRayMap (e*f) R = semilinearDisplayedRayMap e (semilinearDisplayedRayMap f R) := by
  apply Subtype.ext
  change R.val.map (e*f).val.toEmbedding=(R.val.map f.val.toEmbedding).map e.val.toEmbedding
  rw [Finset.map_map]
  rfl

/-- The full untagged semilinear algebra group acts on the actual constructed
ray image. No finite order or scalar-kernel assertion is built into the action. -/
def semilinearDisplayedRayAction : SemilinearAlgebraAutomorphism →* Equiv.Perm DisplayedReflectingRay where
  toFun e :=
    { toFun := semilinearDisplayedRayMap e
      invFun := semilinearDisplayedRayMap e⁻¹
      left_inv := fun R => by rw [← semilinearDisplayedRayMap_mul,inv_mul_cancel,semilinearDisplayedRayMap_one]
      right_inv := fun R => by rw [← semilinearDisplayedRayMap_mul,mul_inv_cancel,semilinearDisplayedRayMap_one] }
  map_one' := by apply Equiv.ext; intro R; exact semilinearDisplayedRayMap_one R
  map_mul' e f := by apply Equiv.ext; intro R; exact semilinearDisplayedRayMap_mul e f R

/-- This kernel is defined by the actual ray action, before proving that its
phases are globally constant. -/
def semilinearRayKernel : Subgroup SemilinearAlgebraAutomorphism := semilinearDisplayedRayAction.ker

theorem mem_semilinearRayKernel_iff (e : SemilinearAlgebraAutomorphism) :
    e ∈ semilinearRayKernel ↔ ∀ t : ReflectingRootParameter,
      rootRay (e.val (reflectingRootParameterVector t))=reflectingRootParameterRay t := by
  change semilinearDisplayedRayAction e=1 ↔ _
  constructor
  · intro he t
    have h := congrArg (fun f : Equiv.Perm DisplayedReflectingRay =>
      (f ⟨reflectingRootParameterRay t,⟨t,rfl⟩⟩).val) he
    change (rootRay (reflectingRootParameterVector t)).map e.val.toEmbedding =
      reflectingRootParameterRay t at h
    rw [semilinearAlgebra_rootRay_map] at h
    exact h
  · intro he
    apply Equiv.ext
    intro R
    apply Subtype.ext
    obtain ⟨t,ht⟩ := R.property
    change R.val.map e.val.toEmbedding=R.val
    rw [← ht]
    exact (semilinearAlgebra_rootRay_map e _).trans (he t)

theorem mem_semilinearRayKernel_phase_iff (e : SemilinearAlgebraAutomorphism) :
    e ∈ semilinearRayKernel ↔ ∀ t : ReflectingRootParameter,
      ∃ a : Scalar, a^3=1 ∧ e.val (reflectingRootParameterVector t)=a • reflectingRootParameterVector t := by
  rw [mem_semilinearRayKernel_iff]
  apply forall_congr'
  intro t
  exact rootRay_eq_iff _ _

end Atlas.Fischer
