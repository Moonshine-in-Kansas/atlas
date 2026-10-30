import Atlas.LinearGroups.PSLFieldTransport
import Atlas.LinearGroups.PSLFamily
import Atlas.LinearGroups.SL2Perfect
import Atlas.FieldTheory.FiniteCubicExtension
import Atlas.GroupTheory.SemidirectDerived

/-! The independent semilinear endpoint for the small Ree comparison.
This is a target construction, not a redefinition or identification of Ree(3). -/
noncomputable section
namespace Atlas.Comparisons.ReeThree
open scoped MatrixGroups
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Actual coefficient-field automorphisms act on the full-center PSL quotient. -/
def fieldAction : (K ≃ₐ[F] K) →* MulAut PSL(2,K) where
  toFun s := Atlas.fieldEquivPSL 2 s.toRingEquiv
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H g =>
      change QuotientGroup.mk (Atlas.fieldEquivSL 2 (1 : K ≃ₐ[F] K).toRingEquiv g) =
        QuotientGroup.mk g
      congr 1
  map_mul' s t := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H g =>
      change QuotientGroup.mk (Atlas.fieldEquivSL 2 (s*t).toRingEquiv g) =
        QuotientGroup.mk (Atlas.fieldEquivSL 2 s.toRingEquiv
          (Atlas.fieldEquivSL 2 t.toRingEquiv g))
      congr 1

abbrev Semilinear := PSL(2,K) ⋊[fieldAction F K] (K ≃ₐ[F] K)

theorem fieldAut_card (hdeg : Module.finrank F K = 3) : Nat.card (K ≃ₐ[F] K) = 3 :=
  (IsGalois.card_aut_eq_finrank F K).trans hdeg

theorem scalar_card (hF : Nat.card F = 2) (hdeg : Module.finrank F K = 3) :
    Nat.card K = 8 := by
  norm_num [Atlas.FiniteCubic.card_extension hdeg,hF]

theorem linearFactor_card (hF : Nat.card F = 2) (hdeg : Module.finrank F K = 3) :
    Nat.card PSL(2,K) = 504 := by
  rw [Atlas.card_psl_factor (F := K) 2, scalar_card F K hF hdeg]
  norm_num [Finset.prod_Icc_succ_top]

theorem semilinear_card (hF : Nat.card F = 2) (hdeg : Module.finrank F K = 3) :
    Nat.card (Semilinear F K) = 1512 := by
  rw [Nat.card_congr (SemidirectProduct.equivProd (φ := fieldAction F K)),
    Nat.card_prod,linearFactor_card F K hF hdeg,fieldAut_card F K hdeg]

theorem linearFactor_simple (hF : Nat.card F = 2) (hdeg : Module.finrank F K = 3) :
    IsSimpleGroup PSL(2,K) :=
  Atlas.psl_simple_rank_two (by rw [scalar_card F K hF hdeg]; decide)

theorem linearFactor_perfect (hF : Nat.card F = 2) (hdeg : Module.finrank F K = 3) :
    Group.IsPerfect PSL(2,K) := by
  letI := Atlas.sl_two_perfect_of_four_le_card (F := K)
    (by rw [scalar_card F K hF hdeg]; decide)
  infer_instance

theorem frobenius_order (hdeg : Module.finrank F K = 3) :
    orderOf (Atlas.FiniteCubic.sigma F K) = 3 := Atlas.FiniteCubic.sigma_order hdeg

theorem frobenius_apply (hF : Nat.card F = 2) (x : K) :
    Atlas.FiniteCubic.sigma F K x = x^2 := by
  rw [Atlas.FiniteCubic.sigma_apply,hF]

theorem semilinear_commutator (hF : Nat.card F = 2) (hdeg : Module.finrank F K = 3) :
    commutator (Semilinear F K) =
      (SemidirectProduct.inl : PSL(2,K) →* Semilinear F K).range := by
  letI := linearFactor_perfect F K hF hdeg
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : IsCyclic (K ≃ₐ[F] K) := isCyclic_of_prime_card (fieldAut_card F K hdeg)
  letI : CommGroup (K ≃ₐ[F] K) := IsCyclic.commGroup
  exact Atlas.GroupTheory.semidirect_commutator_eq_left (fieldAction F K)

/-- Actual inclusion of the PSL factor, with codomain the derived subgroup. -/
def linearFactorEquivDerived (hF : Nat.card F = 2) (hdeg : Module.finrank F K = 3) :
    PSL(2,K) ≃* commutator (Semilinear F K) :=
  (MulEquiv.ofBijective
    (SemidirectProduct.inl : PSL(2,K) →* Semilinear F K).rangeRestrict
    ⟨fun _ _ h => SemidirectProduct.inl_injective (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩).trans
    (MulEquiv.subgroupCongr (semilinear_commutator F K hF hdeg).symm)

theorem semilinear_derived_card (hF : Nat.card F = 2) (hdeg : Module.finrank F K = 3) :
    Nat.card (commutator (Semilinear F K)) = 504 := by
  rw [← Nat.card_congr (linearFactorEquivDerived F K hF hdeg).toEquiv]
  exact linearFactor_card F K hF hdeg

theorem semilinear_derived_simple (hF : Nat.card F = 2) (hdeg : Module.finrank F K = 3) :
    IsSimpleGroup (commutator (Semilinear F K)) := by
  letI := linearFactor_simple F K hF hdeg
  exact (linearFactorEquivDerived F K hF hdeg).symm.isSimpleGroup

end Atlas.Comparisons.ReeThree

