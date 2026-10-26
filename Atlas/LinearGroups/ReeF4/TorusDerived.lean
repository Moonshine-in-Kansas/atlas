import Atlas.LinearGroups.ReeF4.WeylLongest
import Atlas.LinearGroups.ReeF4.WeylModel
import Atlas.LinearGroups.ReeF4.RootGroupMembership
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Units.Equiv

/-! The actual torus lies in the derived subgroup of the intrinsic Ree model.
The longest Weyl element inverts it, and Frobenius supplies square roots in the
finite characteristic-two field. The binary case is included: its torus is trivial.
This does not assert perfectness of the full model. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
open scoped commutatorElement
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The already verified diagonal torus, now valued in the full intrinsic model. -/
def torusModelHom {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    Fˣ × Fˣ →* Model F m where
  toFun p := ⟨torusEquiv m p.1 p.2,torusEquiv_mem_modelSubgroup hcard p.1 p.2⟩
  map_one' := by
    apply Subtype.ext
    exact (torusHom (F := F) m).map_one
  map_mul' p q := by
    apply Subtype.ext
    exact (torusHom (F := F) m).map_mul p q

/-- The actual longest relative Weyl operator, viewed in the intrinsic group. -/
def weylLongestModel (m : ℕ) : Model F m :=
  ⟨weylLongest, by
    change (weylRho * weylSigma)^4 ∈ modelSubgroup F m
    exact (modelSubgroup F m).pow_mem
      ((modelSubgroup F m).mul_mem (weylOperator_mem_modelSubgroup m 0)
        (weylOperator_mem_modelSubgroup m 1)) 4⟩

private theorem torusModelHom_val {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a b : Fˣ) :
    (torusModelHom hcard (a,b)).val = torusEquiv m a b := rfl

private theorem weylLongestModel_val (m : ℕ) :
    (weylLongestModel (F := F) m).val = weylLongest := rfl

theorem torusModelHom_commutator_longest {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a b : Fˣ) :
    ⁅torusModelHom hcard (a,b),weylLongestModel m⁆ =
      (torusModelHom hcard (a,b))^2 := by
  rw [commutatorElement_def]
  apply Subtype.ext
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,Subgroup.coe_pow,
    torusModelHom_val,weylLongestModel_val]
  have hi : weylLongest * (torusEquiv m a b)⁻¹ * weylLongest⁻¹ =
      torusEquiv m a b := by
    have h := congrArg (fun g : TraceZero F ≃ₗ[F] TraceZero F => g⁻¹)
      (weylLongest_torus_inverse m a b)
    simpa only [mul_inv_rev,inv_inv,mul_assoc] using h
  rw [pow_two]
  calc
    _ = torusEquiv m a b *
        (weylLongest * (torusEquiv m a b)⁻¹ * weylLongest⁻¹) := by simp only [mul_assoc]
    _ = torusEquiv m a b * torusEquiv m a b := by rw [hi]

private theorem exists_unit_square (a : Fˣ) : ∃ u : Fˣ, u^2 = a := by
  obtain ⟨u,hu⟩ := (Units.mapEquiv (frobeniusEquiv F 2).toMulEquiv).surjective a
  refine ⟨u,?_⟩
  apply Units.ext
  have h := congrArg (fun z : Fˣ => (z : F)) hu
  change (u : F)^2 = (a : F) at h
  change (u : F)^2 = (a : F)
  exact h

theorem torusModelHom_mem_commutator {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a b : Fˣ) :
    torusModelHom hcard (a,b) ∈ commutator (Model F m) := by
  obtain ⟨u,hu⟩ := exists_unit_square a
  obtain ⟨v,hv⟩ := exists_unit_square b
  have h : ⁅torusModelHom hcard (u,v),weylLongestModel m⁆ ∈ commutator (Model F m) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [torusModelHom_commutator_longest,← map_pow] at h
  have hp : (u,v)^2 = (a,b) := by
    apply Prod.ext
    · exact hu
    · exact hv
  rwa [hp] at h

theorem torusModelHom_range_le_commutator {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    (torusModelHom hcard).range ≤ commutator (Model F m) := by
  rintro _ ⟨⟨a,b⟩,rfl⟩
  exact torusModelHom_mem_commutator hcard a b

end Atlas.ReeF4
