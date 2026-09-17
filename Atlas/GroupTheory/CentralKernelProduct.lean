import Atlas.GroupTheory.KernelComplement
import Mathlib.Algebra.Group.Prod
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.Subgroup.Center

namespace Atlas.GroupTheory

/-- A central complement to a homomorphism kernel gives an actual direct product. -/
noncomputable def centralKernelProductEquiv {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (K : Subgroup G) (hK : K≤Subgroup.center G)
    (hf : Function.Bijective (f.comp K.subtype)) : K × f.ker ≃* G := by
  let m : K × f.ker →* G := MonoidHom.noncommCoprod K.subtype f.ker.subtype
    (fun a b => (Subgroup.mem_center_iff.mp (hK a.prop) b.val).symm)
  exact MulEquiv.ofBijective m
    ((Subgroup.isComplement_iff_bijective _ _).mp
      (isComplement_kernel_of_restriction_bijective f K hf).symm)

end Atlas.GroupTheory
