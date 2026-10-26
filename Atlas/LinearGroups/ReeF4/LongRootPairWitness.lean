import Atlas.LinearGroups.ReeF4.LongRootDomainWitness

/-! The extension ambiguity is detected by an actual admissible pair,
so this local compatibility is required even by the partial-product definition. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert

private abbrev B := ZMod 2

def forcingLeft : TraceZero B := diagonalVector 0 + rootVector (2,0)
def forcingRight : TraceZero B := rootVector (0,7) + rootVector (1,4)
def forcingLeftImage : TraceZero B := longRootImage (.inl 0) + longRootImage (.inr (2,0))
def forcingRightImage : TraceZero B := longRootImage (.inr (0,7)) + longRootImage (.inr (1,4))

theorem forcing_pair : StarDomain forcingLeft forcingRight := by
  unfold StarDomain
  decide

theorem forcing_image_pair : StarDomain forcingLeftImage forcingRightImage := by
  unfold StarDomain
  decide

theorem forcingLeft_transport : longRootLinear forcingLeft = forcingLeftImage := by
  simp [forcingLeft, forcingLeftImage, longRootImage]

theorem forcingRight_transport : longRootLinear forcingRight = forcingRightImage := by
  simp [forcingRight, forcingRightImage]

theorem forcing_diagonal_zero : exteriorDiagonal (wedge forcingLeft forcingRight) = 0 := by
  rw [exteriorDiagonal_wedge]
  decide

theorem forcing_image_diagonal_one :
    exteriorDiagonal (wedge forcingLeftImage forcingRightImage) = 1 := by
  rw [exteriorDiagonal_wedge]
  decide

/-- Only compatibility at this actual admissible pair is required here. -/
theorem extension_unique_of_partial_longRoot
    (f g : StarCarrier (F := B) →ₗ[B] TraceZero B)
    (hk : ∀ x : StarCarrier (F := B), exteriorDiagonal x.val = 0 → f x = g x)
    (hf : f (domainWedge _ _ forcing_image_pair) =
      longRootLinear (f (domainWedge _ _ forcing_pair)))
    (hg : g (domainWedge _ _ forcing_image_pair) =
      longRootLinear (g (domainWedge _ _ forcing_pair))) : f = g := by
  apply Atlas.semilinear_ext_on_kernel_and_unit (RingHom.id B)
    (exteriorDiagonal.comp (StarCarrier (F := B)).subtype) f g
    (domainWedge _ _ forcing_image_pair) forcing_image_diagonal_one hk
  rw [hf, hg, hk (domainWedge _ _ forcing_pair) forcing_diagonal_zero]

end Atlas.ReeF4
