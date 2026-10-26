import Atlas.LinearGroups.SuzukiFamily.GroupRelations
import Atlas.LinearGroups.SuzukiFamily.TorusWeight
import Mathlib.GroupTheory.IsPerfect
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-! Derived subgroup in the ambient matrices and nontrivial torus weights. -/
noncomputable section
namespace Atlas.SuzukiFamily
open scoped commutatorElement
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def derivedAmbient (m : ℕ) : Subgroup (Atlas.Symplectic.Sp 2 F) :=
  (commutator (Group F m)).map (generated m).subtype

theorem commutator_mem_derivedAmbient (m : ℕ) {g h : Atlas.Symplectic.Sp 2 F}
    (hg : g ∈ generated m) (hh : h ∈ generated m) : ⁅g,h⁆ ∈ derivedAmbient m :=
  ⟨⁅(⟨g,hg⟩ : Group F m),⟨h,hh⟩⁆,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _),rfl⟩

theorem conjugate_mem_derivedAmbient (m : ℕ) {g h : Atlas.Symplectic.Sp 2 F}
    (hg : g ∈ generated m) (hh : h ∈ derivedAmbient m) : g*h*g⁻¹ ∈ derivedAmbient m := by
  obtain ⟨x,hx,rfl⟩ := hh
  exact ⟨(⟨g,hg⟩ : Group F m)*x*(⟨g,hg⟩ : Group F m)⁻¹,
    (inferInstance : (commutator (Group F m)).Normal).conj_mem x hx ⟨g,hg⟩,rfl⟩

theorem exists_nontrivial_weights (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (hm : 1≤m) :
    ∃ t : Fˣ, theta F m (t:F)≠1 ∧ (t:F)^2*theta F m (t:F)≠1 := by
  have hc := card_ge_eight hcard hm
  have hu : 1<Nat.card Fˣ := by rw [Nat.card_units]; omega
  letI : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hu
  obtain ⟨t,ht⟩ := exists_ne (1 : Fˣ)
  refine ⟨t,?_,?_⟩
  · intro he
    exact ht (Units.ext ((theta F m).injective (by simpa using he)))
  · intro he
    exact ht (Units.ext (weight_eq_one m hcard (t:F) he))

theorem torus_root_commutator (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (t : Fˣ) (a b : F) :
    ⁅(torusElement m t)⁻¹,rootElement m a b⁆ =
      rootElement m (theta F m (t:F)*a+a)
        ((t:F)^2*theta F m (t:F)*b+(b+a*theta F m a)+
          (theta F m (t:F)*a)*theta F m a) := by
  rw [commutatorElement_def,inv_inv,← torusElement_inv,
    torus_root_conjugate m hcard,rootElement_inv m hcard,rootElement_mul m hcard]
end Atlas.SuzukiFamily
