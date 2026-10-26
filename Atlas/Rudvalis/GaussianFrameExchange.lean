import Atlas.Rudvalis.FrameExchangePower
import Atlas.Rudvalis.GeneratedGroup
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! The frame exchange enters the lattice group only through the independently
constructed glue reflection and the verified ambient word identity. -/
namespace Atlas.Rudvalis

noncomputable def gaussianFrameExchange : gaussianLatticeGroup :=
  codeGaussianHom (codeI*codeI) * codeGaussianHom frameSignCode *
    (codeGaussianHom frameSignCode*rudvalisReflection)^4

theorem gaussianFrameExchange_val : gaussianFrameExchange.val=frameComparison := by
  apply LinearEquiv.ext
  intro v
  have hnegative (w : RationalSpace) : (codeGaussianHom (codeI*codeI)).val w=-w := by
    change rationalMonomialHom (codeI.val*codeI.val) w=-w
    rw [codeI_squared_signed,negativeMonomial_rational]
  simp only [gaussianFrameExchange,Subgroup.coe_mul,Subgroup.coe_pow,LinearEquiv.mul_apply]
  rw [hnegative]
  change -frameSign (((frameSign*distinguishedReflection)^4) v)=frameComparison v
  exact (frameComparison_exchange_identity v).symm

theorem gaussianFrameExchange_mem_generated : gaussianFrameExchange∈generatedGaussianGroup := by
  exact generatedGaussianGroup.mul_mem
    (generatedGaussianGroup.mul_mem (codeGaussianHom_mem_generated _) (codeGaussianHom_mem_generated _))
    (generatedGaussianGroup.pow_mem
      (generatedGaussianGroup.mul_mem (codeGaussianHom_mem_generated _) rudvalisReflection_mem_generated) 4)

theorem frameComparison_lattice_iff (v : RationalSpace) :
    frameComparison v∈rudvalisLattice ↔ v∈rudvalisLattice := by
  rw [←gaussianFrameExchange_val]
  exact (gaussianFrameExchange.prop.2.1 v).symm

theorem frameComparison_gaussian (v : RationalSpace) :
    frameComparison (rationalI v)=rationalI (frameComparison v) := by
  rw [←gaussianFrameExchange_val]
  exact gaussianFrameExchange.prop.2.2 v

theorem gaussianFrameExchange_square : gaussianFrameExchange^2=1 := by
 apply Subtype.ext
 simp only [Subgroup.coe_pow,Subgroup.coe_one]
 rw [gaussianFrameExchange_val]
 apply LinearEquiv.ext
 intro v
 change frameComparison (frameComparison v)=v
 exact frameComparison_involutive v

theorem rudvalisReflection_frameExchange :
    rudvalisReflection=gaussianFrameExchange*codeGaussianHom frameSignCode*gaussianFrameExchange⁻¹ := by
  apply Subtype.ext
  change distinguishedReflection=gaussianFrameExchange.val*frameSign*gaussianFrameExchange.val⁻¹
  rw [gaussianFrameExchange_val]
  exact distinguishedReflection_conjugacy

/-- The independently constructed reflection and the frame exchange generate the same
actual subgroup together with the full coordinate-frame stabilizer. -/
theorem generatedGaussianGroup_eq_frameExchange :
    generatedGaussianGroup=Subgroup.closure (Set.range codeGaussianHom ∪ {gaussianFrameExchange}) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with ⟨h,rfl⟩ | rfl
    · exact Subgroup.subset_closure (Or.inl ⟨h,rfl⟩)
    · rw [rudvalisReflection_frameExchange]
      apply Subgroup.mul_mem
      · apply Subgroup.mul_mem
        · exact Subgroup.subset_closure (Or.inr rfl)
        · exact Subgroup.subset_closure (Or.inl ⟨frameSignCode,rfl⟩)
      · exact Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inr rfl))
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with ⟨h,rfl⟩ | rfl
    · exact codeGaussianHom_mem_generated h
    · exact gaussianFrameExchange_mem_generated

end Atlas.Rudvalis
