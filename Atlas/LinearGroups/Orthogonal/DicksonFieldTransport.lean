import Atlas.LinearGroups.Orthogonal.FullDicksonD
import Atlas.LinearGroups.Orthogonal.ProjectiveFieldTransport

/-! # Field transport of the actual characteristic-two Dickson kernels -/
noncomputable section
namespace Atlas.Orthogonal
variable {F K : Type*} [Field F] [Field K]
variable [CharP F 2] [CharP K 2] [PerfectRing F 2] [PerfectRing K 2]

/-- The actual intrinsic kernel is identified with the existing elementary carrier. -/
def fullDicksonKernelElementaryEquiv (n : ℕ) :
    (fullDicksonD (F := F) n).ker ≃* elementarySubgroup (formD (n + 3) F) :=
  MulEquiv.subgroupCongr (fullDicksonD_kernel_elementary n)

/-- Field transport is inherited from the already constructed semilinear elementary map. -/
def fieldEquivDicksonKernelD (n : ℕ) (e : F ≃+* K) :
    (fullDicksonD (F := F) n).ker ≃* (fullDicksonD (F := K) n).ker :=
  (fullDicksonKernelElementaryEquiv n).trans
    ((fieldEquivElementaryD e).trans (fullDicksonKernelElementaryEquiv n).symm)

/-- The intrinsic transport agrees exactly with transport in the full orthogonal group. -/
theorem fieldEquivDicksonKernelD_full (n : ℕ) (e : F ≃+* K)
    (g : (fullDicksonD (F := F) n).ker) :
    (fieldEquivDicksonKernelD n e g).val = fieldEquivFullD e g.val := rfl

/-- Its elementary identification commutes with the fixed elementary field equivalence. -/
theorem fieldEquivDicksonKernelD_elementary (n : ℕ) (e : F ≃+* K)
    (g : (fullDicksonD (F := F) n).ker) :
    fullDicksonKernelElementaryEquiv n (fieldEquivDicksonKernelD n e g) =
      fieldEquivElementaryD e (fullDicksonKernelElementaryEquiv n g) := rfl

/-- The existing scalar quotient also commutes with this intrinsic field transport. -/
theorem fieldEquivDicksonKernelD_projective (n : ℕ) (e : F ≃+* K)
    (g : (fullDicksonD (F := F) n).ker) :
    fieldEquivProjectiveElementaryD e
      (projectiveElementaryMap _ (fullDicksonKernelElementaryEquiv n g)) =
      projectiveElementaryMap _
        (fullDicksonKernelElementaryEquiv n (fieldEquivDicksonKernelD n e g)) := rfl
end Atlas.Orthogonal
