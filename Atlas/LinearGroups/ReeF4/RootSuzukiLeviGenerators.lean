import Atlas.LinearGroups.ReeF4.RootSuzukiLeviRepresentation

/-! Full 26-coordinate generator comparisons, stronger than restrictions to
one natural block. These identify the actual operators, including the entire
exterior summand and the four pointwise fixed coordinates. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem suzukiLeviHom_root (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b : F) :
    suzukiLeviHom (Atlas.SuzukiFamily.rootElement m a (b+a*theta F m a)) =
      shortRootPairEquiv m hcard a b := by
  apply LinearEquiv.ext
  intro w
  apply suzukiLeviCoordinatesEquiv.injective
  change suzukiLeviCoordinatesEquiv
      (suzukiLeviLinear (Atlas.SuzukiFamily.matrix
        (Atlas.SuzukiFamily.rootElement m a (b+a*theta F m a))) w) = _
  rw [suzukiLeviLinear_coordinates, Atlas.SuzukiFamily.matrix_root]
  apply Prod.ext
  · funext k
    exact (shortRootPairEquiv_suzukiBlock m hcard a b k w).symm
  · apply Prod.ext
    · exact (shortRootPairEquiv_suzukiExterior m hcard a b w).symm
    · exact (shortRootPairLinear_suzukiFixed (theta F m).toRingHom a b w).symm

theorem suzukiLeviHom_weyl :
    suzukiLeviHom (Atlas.SuzukiFamily.weylElement : Atlas.Symplectic.Sp 2 F) =
      weylRho := by
  apply LinearEquiv.ext
  intro w
  apply suzukiLeviCoordinatesEquiv.injective
  change suzukiLeviCoordinatesEquiv
      (suzukiLeviLinear (Atlas.SuzukiFamily.matrix Atlas.SuzukiFamily.weylElement) w) = _
  rw [suzukiLeviLinear_coordinates, Atlas.SuzukiFamily.matrix_weyl]
  apply Prod.ext
  · funext k
    exact (weylRho_suzukiBlock k w).symm
  · apply Prod.ext
    · exact (weylRho_suzukiExterior w).symm
    · exact (weylRho_suzukiFixed w).symm

end Atlas.ReeF4
