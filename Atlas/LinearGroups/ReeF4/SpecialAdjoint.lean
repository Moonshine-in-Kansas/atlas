import Atlas.LinearGroups.ReeF4.SpecialAdjointChecks.Row26
import Atlas.Algebra.Albert.DirectionalCubic

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
/-- The actual Albert adjoint of every raw star output vanishes on the full
domain. No isotropic-input or finite-field assumption enters this identity. -/
theorem rawStar_adjoint_zero (u v : TraceZero F) (h : StarDomain u v) :
    adjoint (proposedStarLinear (wedge u v)).val = 0 := by
  apply Prod.ext
  · funext i
    fin_cases i
    · exact rawStar_adjoint_diag0_zero u v h
    · exact rawStar_adjoint_diag1_zero u v h
    · exact rawStar_adjoint_diag2_zero u v h
  · funext b j
    fin_cases b <;> fin_cases j
    · exact rawStar_adjoint_root2_zero u v h
    · exact rawStar_adjoint_root3_zero u v h
    · exact rawStar_adjoint_root4_zero u v h
    · exact rawStar_adjoint_root5_zero u v h
    · exact rawStar_adjoint_root6_zero u v h
    · exact rawStar_adjoint_root7_zero u v h
    · exact rawStar_adjoint_root8_zero u v h
    · exact rawStar_adjoint_root9_zero u v h
    · exact rawStar_adjoint_root10_zero u v h
    · exact rawStar_adjoint_root11_zero u v h
    · exact rawStar_adjoint_root12_zero u v h
    · exact rawStar_adjoint_root13_zero u v h
    · exact rawStar_adjoint_root14_zero u v h
    · exact rawStar_adjoint_root15_zero u v h
    · exact rawStar_adjoint_root16_zero u v h
    · exact rawStar_adjoint_root17_zero u v h
    · exact rawStar_adjoint_root18_zero u v h
    · exact rawStar_adjoint_root19_zero u v h
    · exact rawStar_adjoint_root20_zero u v h
    · exact rawStar_adjoint_root21_zero u v h
    · exact rawStar_adjoint_root22_zero u v h
    · exact rawStar_adjoint_root23_zero u v h
    · exact rawStar_adjoint_root24_zero u v h
    · exact rawStar_adjoint_root25_zero u v h

theorem proposedPartialProduct_adjoint_zero (σ : F →+* F)
    (u v : TraceZero F) (h : StarDomain u v) :
    adjoint (proposedPartialProduct σ u v h).val = 0 := by
  change adjoint (Atlas.Albert.map σ (proposedStarLinear (wedge u v)).val)=0
  rw [adjoint_map,rawStar_adjoint_zero u v h]
  ext i <;> simp [Atlas.Albert.map]

section FiniteField
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
/-- Intrinsic special vectors have zero Albert adjoint (and are nonzero by
definition). This is a proved rank-one condition, not a redefinition of special. -/
theorem IsSpecialVector.adjoint_zero {m : ℕ} {u : TraceZero K}
    (hu : IsSpecialVector m u) : adjoint u.val = 0 := by
  obtain ⟨_,v,h,he⟩ := hu
  calc
    adjoint u.val = adjoint (proposedPartialProduct (thetaInv K m).toRingHom u v h).val :=
      congrArg (fun w : TraceZero K => adjoint w.val) he
    _ = 0 := proposedPartialProduct_adjoint_zero _ u v h
end FiniteField
end Atlas.ReeF4
