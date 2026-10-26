import Atlas.LinearGroups.ReeF4.NonisotropicDomain
import Atlas.LinearGroups.ReeF4.ExteriorDomain

/-! A diagonal exterior coordinate detecting a missing component in basis-pair rules. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def diagonalAlternating : (TraceZero F) [⋀^Fin 2]→ₗ[F] F where
  toFun v := (v 0).val.1 0 * (v 1).val.1 1 - (v 0).val.1 1 * (v 1).val.1 0
  map_update_add' v i x y := by
    fin_cases i <;> simp <;> ring
  map_update_smul' v i a x := by
    fin_cases i <;> simp [smul_eq_mul] <;> ring
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j <;> simp_all <;> ring

def exteriorDiagonal : (⋀[F]^2 (TraceZero F)) →ₗ[F] F :=
  exteriorPower.alternatingMapLinearEquiv diagonalAlternating

@[simp] theorem exteriorDiagonal_wedge (u v : TraceZero F) :
    exteriorDiagonal (wedge u v) = u.val.1 0 * v.val.1 1 - u.val.1 1 * v.val.1 0 := by
  simp [exteriorDiagonal, wedge, diagonalAlternating]

@[simp] theorem exteriorDiagonal_root_left (r : ShortRootLabel) (v : TraceZero F) :
    exteriorDiagonal (wedge (rootVector r) v) = 0 := by
  simp [rootVector]

@[simp] theorem exteriorDiagonal_root_right (u : TraceZero F) (r : ShortRootLabel) :
    exteriorDiagonal (wedge u (rootVector r)) = 0 := by
  simp [rootVector]

theorem exteriorDiagonal_domain_witness :
    exteriorDiagonal (wedge nonsingularDomainLeft nonsingularDomainRight) = 1 := by
  rw [exteriorDiagonal_wedge]
  decide

/-- Root-containing basis wedges do not span the entire assigned star domain. -/
theorem domain_not_spanned_by_root_wedges :
    ¬ StarCarrier (F := ZMod 2) ≤ Submodule.span (ZMod 2)
      {x | ∃ r : ShortRootLabel, ∃ v : TraceZero (ZMod 2),
        x = wedge (rootVector r) v ∨ x = wedge v (rootVector r)} := by
  intro h
  have hs : Submodule.span (ZMod 2)
      {x | ∃ r : ShortRootLabel, ∃ v : TraceZero (ZMod 2),
        x = wedge (rootVector r) v ∨ x = wedge v (rootVector r)} ≤ exteriorDiagonal.ker := by
    apply Submodule.span_le.mpr
    rintro x ⟨r,v,hv | hv⟩ <;> subst x <;> simp [LinearMap.mem_ker, rootVector]
  have hx := hs (h ((wedge_mem_starCarrier_iff _ _).mpr nonsingularDomain_pair))
  rw [LinearMap.mem_ker, exteriorDiagonal_domain_witness] at hx
  exact one_ne_zero hx

end Atlas.ReeF4
