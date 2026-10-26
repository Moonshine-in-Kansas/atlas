import Atlas.LinearGroups.ReeF4.DiagonalProductTables

/-! The prescribed domain includes pairs with a nonsingular quadratic member. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert

def nonsingularDomainLeft : TraceZero (ZMod 2) :=
  diagonalVector 0 + rootVector (0,0) + rootVector (1,0) + rootVector (2,4)

def nonsingularDomainRight : TraceZero (ZMod 2) :=
  diagonalVector 1 + rootVector (0,7) + rootVector (1,0) + rootVector (1,7) + rootVector (2,3)

theorem nonsingularDomain_pair : StarDomain nonsingularDomainLeft nonsingularDomainRight := by
  unfold StarDomain
  decide

theorem nonsingularDomain_quadratic : traceZeroQuadratic nonsingularDomainLeft = 1 := by
  decide

theorem domain_not_quadratic_isotropic :
    ¬ (∀ u v : TraceZero (ZMod 2), StarDomain u v → traceZeroQuadratic u = 0) := by
  intro h
  have hh := h nonsingularDomainLeft nonsingularDomainRight nonsingularDomain_pair
  rw [nonsingularDomain_quadratic] at hh
  exact one_ne_zero hh

end Atlas.ReeF4
